use std::error::Error;

#[derive(Debug)]
pub struct Decline(pub String);

impl std::fmt::Display for Decline {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "declined: {}", self.0)
    }
}

impl Error for Decline {}

pub(crate) fn decline<A>(msg: impl Into<String>) -> Result<A, Box<dyn Error>> {
    Err(Box::new(Decline(msg.into())))
}
