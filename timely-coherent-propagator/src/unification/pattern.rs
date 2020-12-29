//! Patterns describe expectations to match against (yielding
//! Captures), or, symmetrically, templates to populate from
//! Substitutions.
use super::MetaVar;
use crate::ground::{Capture, Fact, Variable};
use std::convert::TryFrom;

/// A match pattern (or template...) is a slice of references to
/// metavariables.  When a reference appears multiple times, it must
/// match against (be populated with) the same ground variable.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Element {
    /// References may match any ground variable, but references with
    /// the same metavariable must match the same ground variable.
    Reference(MetaVar),
}

/// Once instantiated, a pattern takes a Fact (which must match the
/// number of elements passed to `new`), and attempts to make it fit
/// the elements.  On success, the result is a capture.
pub struct Pattern {
    input_len: usize,
    output: Vec<MetaVar>,
    fun: Box<dyn Fn(&Fact) -> Option<Capture>>,
}

impl Pattern {
    /// Constructs a new pattern that attempts to match Facts against
    /// the `pattern` elements.
    ///
    /// # Errors
    ///
    /// Does not currently fail.
    pub fn new(pattern: &[Element]) -> Result<Self, &'static str> {
        Ok(make_pattern(pattern))
    }

    /// The input `Fact`s passed to `try_match` must have the same
    /// number of Variables as `input_len`, the number of Elements in
    /// the instantiation pattern.
    #[must_use]
    pub fn input_len(&self) -> usize {
        self.input_len
    }

    #[must_use]
    pub fn output(&self) -> &[MetaVar] {
        &self.output
    }

    #[inline]
    #[must_use]
    pub fn try_match(&self, fact: &Fact) -> Option<Capture> {
        (self.fun)(fact)
    }
}

fn make_pattern(pattern: &[Element]) -> Pattern {
    // Represent indices as u8 for density.
    let mut match_variables = Vec::<MetaVar>::new();

    for Element::Reference(mv) in pattern.iter() {
        match_variables.push(mv.clone());
    }

    match_variables.sort();
    match_variables.dedup();

    // The first item in the tuple is the source index,
    // the last is the destination index.
    let mut match_indices = Vec::<(u8, u8)>::new();
    for (src_index, elt) in pattern.iter().enumerate() {
        let Element::Reference(mv) = elt;
        let dst_index = match_variables.binary_search(mv).expect("must be found");
        match_indices.push((
            u8::try_from(src_index).expect("Wide source capture not supported"),
            u8::try_from(dst_index).expect("Wide destination capture not supported"),
        ));
    }

    let num = pattern.len();
    let match_size = match_variables.len();
    let matcher = move |fact: &Fact| {
        let vars = fact.vars();

        assert_eq!(vars.len(), num);

        let mut ret = Vec::<Variable>::with_capacity(match_size);
        ret.resize(match_size, Variable::uninit());

        for (in_index, ret_index) in match_indices.iter().cloned() {
            let actual = vars[in_index as usize];
            let prev = ret[ret_index as usize];

            if prev != Variable::uninit() && actual != prev {
                return None;
            }

            ret[ret_index as usize] = actual;
        }

        Some(Capture::from_vec(ret))
    };

    Pattern {
        input_len: pattern.len(),
        output: match_variables,
        fun: Box::new(matcher),
    }
}

#[test]
fn test_pattern_match_happy_path() {
    use super::Projection;

    let x = MetaVar::new("x");
    let y = MetaVar::new("y");

    let pattern = Pattern::new(&[
        Element::Reference(x.clone()),
        Element::Reference(y.clone()),
        Element::Reference(x.clone()),
    ])
    .expect("ok");

    assert_eq!(pattern.input_len(), 3);
    assert_eq!(pattern.output().len(), 2);

    let extract_x = Projection::new(pattern.output(), &[x.clone()]).expect("ok");
    let extract_y = Projection::new(pattern.output(), &[y.clone()]).expect("ok");

    let args: Fact = [2, 3, 2]
        .iter()
        .map(|i| Variable::new(*i))
        .collect::<Vec<_>>()
        .into();
    let extracted = pattern.try_match(&args).expect("matches");

    assert_eq!(extract_x.apply(&extracted), [Variable::new(2)].into());
    assert_eq!(extract_y.apply(&extracted), [Variable::new(3)].into());
}

#[test]
fn test_pattern_match_mismatch() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");

    let pattern = Pattern::new(&[
        Element::Reference(x.clone()),
        Element::Reference(y.clone()),
        Element::Reference(x.clone()),
    ])
    .expect("ok");

    let args2: Fact = [2, 3, 4]
        .iter()
        .map(|i| Variable::new(*i))
        .collect::<Vec<_>>()
        .into();
    assert_eq!(pattern.try_match(&args2), None);
}
