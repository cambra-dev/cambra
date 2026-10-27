//! The thread-safe handles the interpreter shares between operators, consumers and the
//! scheduler. See `src/interpreter/design-parallel.md`, "Thread-safe handles".

use std::sync::{Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard, TryLockError};

/// Lock a cell that is held by no one else, or panic naming the cell.
///
/// A lock is never waited for: in a single-threaded run a lock that is already held is a
/// re-entrant access, which `RefCell` reported as a panic and which a blocking lock would turn
/// into a deadlock. A site two threads contend on takes a blocking lock when that site exists.
pub trait LockNow<T: ?Sized> {
    /// The guard, or a panic naming the cell when it is already locked.
    fn lock_now(&self) -> MutexGuard<'_, T>;

    /// The guard, or `None` when the cell is already locked: the re-entry test a notification
    /// forwarder makes.
    fn try_lock_now(&self) -> Option<MutexGuard<'_, T>>;

    /// The guard, waiting for another thread to release it: for a cell worker threads contend
    /// on, which is never locked twice by one thread.
    fn lock_wait(&self) -> MutexGuard<'_, T>;
}

impl<T: ?Sized> LockNow<T> for Mutex<T> {
    fn lock_now(&self) -> MutexGuard<'_, T> {
        match self.try_lock() {
            Ok(guard) => guard,
            // A panic while the lock was held poisons it. The value is whatever the panicking
            // holder left, and handing it out is right: the `Drop` impls that lock a fan's
            // state run during that unwind, and the panic that poisoned it is the failure to
            // report, not this one.
            Err(TryLockError::Poisoned(poisoned)) => poisoned.into_inner(),
            Err(TryLockError::WouldBlock) => panic!(
                "a cell of {} is locked while it is locked again: a re-entrant access",
                std::any::type_name::<T>()
            ),
        }
    }

    fn try_lock_now(&self) -> Option<MutexGuard<'_, T>> {
        match self.try_lock() {
            Ok(guard) => Some(guard),
            Err(TryLockError::Poisoned(poisoned)) => Some(poisoned.into_inner()),
            Err(TryLockError::WouldBlock) => None,
        }
    }

    fn lock_wait(&self) -> MutexGuard<'_, T> {
        self.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
    }
}

/// A `Copy` value with `Cell`'s interface behind a lock: the counters and flags a test double
/// shares between a producer and the test that reads it.
#[cfg(test)]
pub(crate) struct SyncCell<T>(Mutex<T>);

#[cfg(test)]
impl<T: Copy> SyncCell<T> {
    pub fn new(value: T) -> Self {
        Self(Mutex::new(value))
    }

    pub fn get(&self) -> T {
        *self.0.lock_now()
    }

    pub fn set(&self, value: T) {
        *self.0.lock_now() = value;
    }

    /// Store `value` and return what was there.
    pub fn replace(&self, value: T) -> T {
        std::mem::replace(&mut *self.0.lock_now(), value)
    }
}

/// The read-or-panic and write-or-panic of [`LockNow`], for an `RwLock`: the cell an operator
/// is held in by a fan or a `CycleSlot`, whose readers nest.
pub trait ReadNow<T: ?Sized> {
    /// A read guard; nests with other read guards, panics on a held write guard.
    fn read_now(&self) -> RwLockReadGuard<'_, T>;

    /// A write guard, or a panic naming the cell when any guard is held.
    fn write_now(&self) -> RwLockWriteGuard<'_, T>;
}

impl<T: ?Sized> ReadNow<T> for RwLock<T> {
    fn read_now(&self) -> RwLockReadGuard<'_, T> {
        match self.try_read() {
            Ok(guard) => guard,
            Err(TryLockError::Poisoned(poisoned)) => poisoned.into_inner(),
            Err(TryLockError::WouldBlock) => panic!(
                "a cell of {} is read while it is written: a re-entrant access",
                std::any::type_name::<T>()
            ),
        }
    }

    fn write_now(&self) -> RwLockWriteGuard<'_, T> {
        match self.try_write() {
            Ok(guard) => guard,
            Err(TryLockError::Poisoned(poisoned)) => poisoned.into_inner(),
            Err(TryLockError::WouldBlock) => panic!(
                "a cell of {} is written while it is held: a re-entrant access",
                std::any::type_name::<T>()
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    #[should_panic(expected = "re-entrant access")]
    fn a_held_cell_locked_again_panics() {
        let cell = Mutex::new(0u8);
        let _held = cell.lock_now();
        let _again = cell.lock_now();
    }

    #[test]
    fn try_lock_now_answers_none_while_held() {
        let cell = Mutex::new(0u8);
        let held = cell.lock_now();
        assert!(cell.try_lock_now().is_none());
        drop(held);
        assert!(cell.try_lock_now().is_some());
    }

    #[test]
    fn a_poisoned_cell_hands_out_what_the_panic_left() {
        let cell = Arc::new(Mutex::new(1u8));
        let poisoner = cell.clone();
        let _ = std::thread::spawn(move || {
            *poisoner.lock_now() = 2;
            panic!("poison");
        })
        .join();
        assert_eq!(*cell.lock_now(), 2);
        assert!(cell.try_lock_now().is_some());
    }

    #[test]
    fn read_guards_nest() {
        let cell = RwLock::new(0u8);
        let _a = cell.read_now();
        let _b = cell.read_now();
    }

    #[test]
    #[should_panic(expected = "re-entrant access")]
    fn a_write_under_a_read_panics() {
        let cell = RwLock::new(0u8);
        let _read = cell.read_now();
        let _write = cell.write_now();
    }
}
