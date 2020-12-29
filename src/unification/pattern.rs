//! Patterns describe expectations to match against (yielding
//! Captures), or, symmetrically, templates to populate from
//! Substitutions.
use super::MetaVar;
use crate::ground::{Capture, Fact, Variable};

/// A match pattern (or template...) is a slice of constant values and
/// references to metavariables.  When a reference appears multiple
/// times, it must match against (be populated with) the same ground
/// variable.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Element {
    /// Constants must match the literal ground variable exactly.
    Constant(Variable),
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
    pub fn new(pattern: &[Element]) -> Result<Self, &'static str> {
        Ok(make_pattern(pattern))
    }

    /// The input `Fact`s passed to `try_match` must have the same
    /// number of Variables as `input_len`, the number of Elements in
    /// the instantiation pattern.
    pub fn input_len(&self) -> usize {
        self.input_len
    }

    pub fn output(&self) -> &[MetaVar] {
        &self.output
    }

    #[inline]
    pub fn try_match(&self, fact: &Fact) -> Option<Capture> {
        (self.fun)(fact)
    }
}

fn make_pattern(pattern: &[Element]) -> Pattern {
    // Represent indices as u8 or u32 (when u8 would be padded anyway)
    // for density.
    let mut constants = Vec::<(u32, Variable)>::new();
    let mut match_variables = Vec::<MetaVar>::new();

    for (index, elt) in pattern.iter().enumerate() {
        assert!(index <= u32::MAX as usize);
        match elt {
            Element::Constant(var) => constants.push((index as u32, *var)),
            Element::Reference(mv) => match_variables.push(mv.clone()),
        }
    }

    match_variables.sort();
    match_variables.dedup();

    // The first item in the tuple is the source index,
    // the last is the destination index.
    let mut match_indices = Vec::<(u8, u8)>::new();
    for (src_index, elt) in pattern.iter().enumerate() {
        if let Element::Reference(mv) = elt {
            let dst_index = match_variables.binary_search(mv).expect("must be found");
            assert!(src_index <= u8::MAX as usize);
            assert!(dst_index <= u8::MAX as usize);
            match_indices.push((src_index as u8, dst_index as u8));
        }
    }

    let num = pattern.len();
    let match_size = match_variables.len();
    let matcher = move |fact: &Fact| {
        let vars = fact.vars();

        assert_eq!(vars.len(), num);
        for (index, expected) in constants.iter().copied() {
            if vars[index as usize] != expected {
                return None;
            }
        }

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
        Element::Constant(Variable::new(1)),
        Element::Reference(x.clone()),
        Element::Reference(y.clone()),
        Element::Reference(x.clone()),
    ])
    .expect("ok");

    assert_eq!(pattern.input_len(), 4);
    assert_eq!(pattern.output().len(), 2);

    let extract_x = Projection::new(pattern.output(), &[x.clone()]).expect("ok");
    let extract_y = Projection::new(pattern.output(), &[y.clone()]).expect("ok");

    let args: Fact = [1, 2, 3, 2]
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
        Element::Constant(Variable::new(1)),
        Element::Reference(x.clone()),
        Element::Reference(y.clone()),
        Element::Reference(x.clone()),
    ])
    .expect("ok");

    let args1: Fact = [2, 2, 3, 2]
        .iter()
        .map(|i| Variable::new(*i))
        .collect::<Vec<_>>()
        .into();
    assert_eq!(pattern.try_match(&args1), None);

    let args2: Fact = [1, 2, 3, 4]
        .iter()
        .map(|i| Variable::new(*i))
        .collect::<Vec<_>>()
        .into();
    assert_eq!(pattern.try_match(&args2), None);
}
