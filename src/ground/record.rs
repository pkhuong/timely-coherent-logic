//! A record of ground variables is a key value for our implementation
//! of Coherent Logic: facts (axioms or derived), as well as temporary
//! pattern matching captures are represented as containers of records
//! of variables, with additional shape metadata (e.g., predicate name
//! and arity, or list of bound metavariables) stored next to the
//! container.
//!
//! It is thus important for records to be as lightweight as possible,
//! and we implement them as boxed slices of variables (with explicit
//! clone, which should be avoided in inner loops).

use super::Variable;
// This I/O stuff is only needed for the stub Abomonation trait
// implementation.
use std::io::Result as IOResult;
use std::io::Write;

// We should not need to implement these traits for a phantom type,
// but https://github.com/rust-lang/rust/issues/26925...
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FactTag;
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CaptureTag;

/// A fact is a predicate that is known to be true for a given list of
/// variables.  In our representation, the predicate is tracked
/// separately from the (container of) lists of variables, and a fact
/// is thus only a record of variables.
pub type Fact = Record<FactTag>;

/// A capture represents the actual variables that matched a given
/// pattern.  The corresponding metavariables must be tracked
/// separately from `Capture`s themselves.
pub type Capture = Record<CaptureTag>;

/// A Record is a type-tagged pointer to a slice of Variables.  We use
/// type tags to avoid accidental compatibility between records that
/// represent different data.
///
/// ```compile_fail
/// use timely_coherent_logic::ground::{Capture, Fact};
/// fn mismatch(fact: &Fact, capture: &Capture) -> bool {
///     fact == capture
/// }
/// ```
///
/// TODO: consider pre-computing a fingerprint for fast
///   hashing and comparison.
///
/// TODO: we know that `Variable`s are small (smaller than a pointer +
///   size); a specialised representation for few variables (<= 3-4)
///   would make sense.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Record<Tag: 'static> {
    tag: std::marker::PhantomData<&'static Tag>,
    vars: Box<[Variable]>,
}

impl<Tag> Record<Tag> {
    #[inline]
    pub fn from_vec(vec: Vec<Variable>) -> Self {
        Self {
            tag: std::marker::PhantomData,
            vars: vec.into_boxed_slice(),
        }
    }

    #[inline]
    pub fn from_box(vars: Box<[Variable]>) -> Self {
        Self {
            tag: std::marker::PhantomData,
            vars,
        }
    }

    #[inline]
    pub fn from_slice(vars: &[Variable]) -> Self {
        Self::from_vec(vars.iter().copied().collect::<Vec<_>>())
    }

    #[inline]
    pub fn vars(&self) -> &[Variable] {
        &self.vars
    }
}

impl<T, Tag> From<T> for Record<Tag>
where
    T: Sized + AsRef<[Variable]>,
{
    #[inline]
    fn from(slice: T) -> Self {
        Self::from_slice(slice.as_ref())
    }
}

/// Differential Dataflow has a hard requirement on "Abomonating" data
/// in Collection, but we don't exercise the logic that actually
/// abomonates.
#[cfg(not(tarpaulin_include))]
impl<Tag> abomonation::Abomonation for Record<Tag> {
    unsafe fn entomb<W: Write>(&self, _write: &mut W) -> IOResult<()> {
        panic!("Abomonation not implemented for Records.");
    }

    unsafe fn exhume<'a, 'b>(&'a mut self, _bytes: &'b mut [u8]) -> Option<&'b mut [u8]> {
        panic!("Abomonation not implemented for Records.");
    }

    fn extent(&self) -> usize {
        panic!("Abomonation not implemented for Records.");
    }
}

#[test]
fn construct() {
    let v1 = Variable::fresh();
    let v2 = Variable::fresh();
    let from_vec: Fact = vec![v1, v2].into();
    assert_eq!(from_vec, Fact::from_vec(vec![v1, v2]));

    let from_box: Fact = vec![v1, v2].into_boxed_slice().into();
    assert_eq!(from_box, Fact::from_box(vec![v1, v2].into_boxed_slice()));

    let from_slice: Fact = [v1, v2].into();
    assert_eq!(from_slice, Fact::from_slice(&[v1, v2]));

    assert_eq!(from_vec, from_box);
    assert_eq!(from_vec, from_slice);

    assert_eq!(from_vec.vars()[0], v1);
    assert_eq!(from_vec.vars()[1], v2);
}

#[test]
fn eq() {
    let v1 = Variable::fresh();
    let v2 = Variable::fresh();

    assert_ne!(Fact::from_slice(&[v1, v2]), Fact::from_slice(&[v1, v1]));
    assert_eq!(
        Capture::from_slice(&[v1, v2]),
        Capture::from_slice(&[v1, v2])
    );
}
