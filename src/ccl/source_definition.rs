use super::Type;
use crate::interpreter::DataSourceDomainExtentImpl;
use std::sync::Arc;
use std::sync::PoisonError;
use std::sync::RwLock;

/// Compiler type metadata and the synchronized runtime source it describes.
pub struct SourceDefinition<S: DataSourceDomainExtentImpl + ?Sized = dyn DataSourceDomainExtentImpl>
{
    source: Arc<RwLock<S>>,
    output_type: Type,
}

impl<S: DataSourceDomainExtentImpl> SourceDefinition<S> {
    pub fn new(source: S, output_type: Type) -> Self {
        Self {
            source: Arc::new(RwLock::new(source)),
            output_type,
        }
    }
}
impl<S: DataSourceDomainExtentImpl + ?Sized> SourceDefinition<S> {
    pub fn runtime(&self) -> Arc<RwLock<S>> {
        self.source.clone()
    }
    pub fn output_type(&self) -> Type {
        self.output_type.clone()
    }
}
impl<S: DataSourceDomainExtentImpl + ?Sized> Clone for SourceDefinition<S> {
    fn clone(&self) -> Self {
        Self {
            source: self.source.clone(),
            output_type: self.output_type.clone(),
        }
    }
}
impl<S: DataSourceDomainExtentImpl + ?Sized> SourceDefinition<S> {
    /// A handle that does not keep the source alive, for a test that checks nothing else does.
    #[cfg(test)]
    pub(crate) fn downgrade(&self) -> std::sync::Weak<RwLock<S>> {
        Arc::downgrade(&self.source)
    }
}
impl<S: DataSourceDomainExtentImpl + ?Sized> std::ops::Deref for SourceDefinition<S> {
    type Target = RwLock<S>;
    fn deref(&self) -> &Self::Target {
        &self.source
    }
}
impl<S: DataSourceDomainExtentImpl + 'static> From<SourceDefinition<S>> for SourceDefinition {
    fn from(source: SourceDefinition<S>) -> Self {
        Self {
            source: source.source,
            output_type: source.output_type,
        }
    }
}
/// Type metadata supplied by a source whose type can be constructed without retained compiler state.
pub trait SourceType: DataSourceDomainExtentImpl {
    fn output_type(&self) -> Type;
}
impl<S: SourceType + 'static> From<Arc<RwLock<S>>> for SourceDefinition {
    fn from(source: Arc<RwLock<S>>) -> Self {
        let output_type = source
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .output_type();
        Self {
            source,
            output_type,
        }
    }
}
