//! The execution layer briges the narrow gap between our query plans
//! and differential dataflow's collections.
mod split_containers;

pub use split_containers::CaptureCollection;
pub use split_containers::CaptureVariable;
pub use split_containers::FactCollection;
pub use split_containers::FactVariable;
