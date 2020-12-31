//! The execution layer briges the narrow gap between our query plans
//! and differential dataflow's collections.
mod lower_plan;
mod sink;
mod split_containers;

pub use lower_plan::lower_matching_plan;
pub use sink::sink_all_collections;
pub use sink::CaptureSink;
pub use sink::CaptureWriter;
pub use sink::FactSink;
pub use sink::FactWriter;
pub use split_containers::CaptureCollection;
pub use split_containers::CaptureVariable;
pub use split_containers::FactCollection;
pub use split_containers::FactVariable;
