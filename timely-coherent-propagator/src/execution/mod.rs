//! The execution layer briges the narrow gap between our query plans
//! and differential dataflow's collections.
mod enumerate_candidates;
mod instantiate_conjuncts;
mod lower_plan;
mod sink;
mod split_container;
mod trivial;

pub use enumerate_candidates::enumerate_instantiation_candidates;
pub use enumerate_candidates::SearchSequent;
pub use instantiate_conjuncts::push_conjunct_instances;
pub use instantiate_conjuncts::reify_conjunct_instances;
pub use lower_plan::default_injector;
pub use lower_plan::lower_matching_plan;
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
pub use trivial::saturate_trivialities;
pub use trivial::TrivialSequent;
