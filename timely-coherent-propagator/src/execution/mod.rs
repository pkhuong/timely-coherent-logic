//! The execution layer briges the narrow gap between our query plans
//! and differential dataflow's collections.
mod sink;
mod split_container;

pub use sink::sink_all_collections;
pub use sink::CaptureSink;
pub use sink::CaptureWriter;
pub use sink::FactSink;
pub use sink::FactWriter;
pub use split_container::CaptureCollection;
pub use split_container::CaptureInput;
pub use split_container::CaptureVariable;
pub use split_container::FactCollection;
pub use split_container::FactInput;
pub use split_container::FactVariable;
