use thiserror::Error;

#[derive(Error)]
pub enum Error {
    #[error("Could not find home directory from $HOME env var")]
    NoHomeDirectoryFound,

    #[error("std::io::Error{{ {0} }}")]
    Io(#[from] std::io::Error),

    #[error("ELF Error{{ {0} }}")]
    ELFError(#[from] object::Error),

    #[error("gimli::Error{{ {0} }}")]
    DWARFError(#[from] gimli::Error),
}

impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}
