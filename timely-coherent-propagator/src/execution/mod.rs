//! The execution layer briges the narrow gap between our query plans
//! and differential dataflow's collections.
mod split_container;

pub use split_container::CaptureCollection;
pub use split_container::CaptureInput;
pub use split_container::CaptureVariable;
pub use split_container::FactCollection;
pub use split_container::FactInput;
pub use split_container::FactVariable;
