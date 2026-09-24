//! The message a caught panic carried, shared by the test crates that catch one.

use std::any::Any;

/// Extract a readable string from a `catch_unwind` payload. A panic carries a `String` or a
/// `&'static str`; anything else answers a placeholder, so a test keeps its diagnostic.
pub fn panic_message(payload: &(dyn Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else if let Some(s) = payload.downcast_ref::<&'static str>() {
        s.to_string()
    } else {
        "<non-string panic payload>".to_string()
    }
}
