//! As part of the join logic, we must restructure matches by removing
//! or re-ordering metavariables, and applying the same transformation
//! to individual captures (lists of variables).
use super::MetaVar;
use crate::ground::{Capture, Variable};

/// A Projection takes a single capture (with shape `input`), and
/// returns an output of shape `output`.
pub struct Projection {
    input: Vec<MetaVar>,
    output: Vec<MetaVar>,
    fun: Box<dyn Fn(&Capture) -> Capture>,
}

impl Projection {
    /// Returns a Projection from `inp` into `out`.  This function may fail
    /// if `out` refers to a metavariable absent from `inp`.
    pub fn new(inp: &[MetaVar], out: &[MetaVar]) -> Result<Projection, &'static str> {
        make_projection(inp, out)
    }

    pub fn input(&self) -> &[MetaVar] {
        &self.input
    }

    pub fn output(&self) -> &[MetaVar] {
        &self.output
    }

    #[inline]
    pub fn apply(&self, input: &Capture) -> Capture {
        (self.fun)(input)
    }
}

fn make_projection(inp: &[MetaVar], out: &[MetaVar]) -> Result<Projection, &'static str> {
    let find_index = |needle: &MetaVar| {
        for (index, haystack) in inp.iter().enumerate() {
            if haystack == needle {
                return Ok(index);
            }
        }

        Err("Needle not found in the input haystack")
    };

    // The `indices` vector tells us where to find each output value
    // in the input `Capture`: the first value is the index of the
    // first output, second value that of the second output, etc.
    // Store these indices in a vector of u8: we don't expect very
    // wide fact tables.
    let mut indices = Vec::<u8>::with_capacity(inp.len());
    for needle in out.iter() {
        let index = find_index(needle)?;
        assert!(index <= u8::MAX as usize);
        indices.push(index as u8);
    }

    let expected_input_len = inp.len();
    let output_len = indices.len();
    let projector = move |capture: &Capture| {
        let vars = capture.vars();
        let mut result = Vec::<Variable>::with_capacity(output_len);

        assert_eq!(vars.len(), expected_input_len);
        for index in indices.iter().cloned() {
            result.push(vars[index as usize]);
        }

        Capture::from_vec(result)
    };

    Ok(Projection {
        input: inp.into(),
        output: out.into(),
        fun: Box::new(projector),
    })
}

/// A MultiProjection projects a single capture from any number of
/// captures.  This operation is useful to convert a pair (or
/// arbitrary tuple) of captures into a single capture, after joining
/// them on a common projected key.
pub struct MultiProjection {
    inputs: Vec<Box<[MetaVar]>>,
    output: Vec<MetaVar>,
    fun: Box<dyn Fn(&[&Capture]) -> Capture>,
}

impl MultiProjection {
    /// Returns a MultiProjection from `inp`s into `out`.  This function
    /// may fail if `out` refers to a metavariable absent from all `inp`s.
    ///
    /// The MultiProjection does not check that the input Captures
    /// match the pattern defined in `inp`; the caller is responsible
    /// for enforcing that relationship, e.g., by matching Captures
    /// with a join on common variables.
    pub fn new(inp: &[Box<[MetaVar]>], out: &[MetaVar]) -> Result<MultiProjection, &'static str> {
        make_multi_projection(inp, out)
    }

    pub fn inputs(&self) -> &[Box<[MetaVar]>] {
        &self.inputs
    }

    pub fn output(&self) -> &[MetaVar] {
        &self.output
    }

    #[inline]
    pub fn apply(&self, input: &[&Capture]) -> Capture {
        (self.fun)(input)
    }

    #[inline]
    pub fn from_pair(&self, x: &Capture, y: &Capture) -> Capture {
        self.apply(&[x, y])
    }
}

fn make_multi_projection(
    inp: &[Box<[MetaVar]>],
    out: &[MetaVar],
) -> Result<MultiProjection, &'static str> {
    // Given an output metavariable, finds out which input and where
    // in that input the corresponding value may be found.
    let find_indices = |needle: &MetaVar| {
        for (input_id, input) in inp.iter().enumerate() {
            for (index, haystack) in input.iter().enumerate() {
                if haystack == needle {
                    return Ok((input_id, index));
                }
            }
        }

        Err("Needle not found in the input haystack")
    };

    // The `indices` vector tells us where to find each output value
    // in the input `Capture`.  Each value is a pair of index in the
    // list of input, and index in that input.  The first value is the
    // index of the first output, second value that of the second
    // output, etc.
    //
    // Store these indices in u8: we don't expect very wide joins or
    // tables.
    let mut indices = Vec::<(u8, u8)>::with_capacity(inp.len());
    for needle in out.iter() {
        let (input_id, index) = find_indices(needle)?;
        assert!(input_id <= u8::MAX as usize);
        assert!(index <= u8::MAX as usize);
        indices.push((input_id as u8, index as u8));
    }

    let expected_input_len = inp.len();
    let output_len = indices.len();
    let projector = move |captures: &[&Capture]| {
        let mut result = Vec::<Variable>::with_capacity(output_len);

        assert_eq!(captures.len(), expected_input_len);
        for (input_id, index) in indices.iter().cloned() {
            result.push(captures[input_id as usize].vars()[index as usize]);
        }

        Capture::from_vec(result)
    };

    Ok(MultiProjection {
        inputs: inp.into(),
        output: out.into(),
        fun: Box::new(projector),
    })
}

#[test]
fn test_project_happy_path() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");
    let input = vec![x.clone(), y.clone(), z.clone()];
    let output = vec![z, y];

    let projection = Projection::new(&input, &output).expect("ok");
    assert_eq!(projection.input(), input);
    assert_eq!(projection.output(), output);
    assert_eq!(
        projection.apply(&[Variable::new(1), Variable::new(2), Variable::new(3)].into()),
        vec![Variable::new(3), Variable::new(2)].into()
    );

    // Apply the projection multiple times.
    assert_eq!(
        projection.apply(&[Variable::new(2), Variable::new(3), Variable::new(4)].into()),
        vec![Variable::new(4), Variable::new(3)].into()
    );
}

#[test]
fn test_project_missing_variable() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");
    let input = vec![x.clone(), y.clone()];
    let output = vec![z, y];

    assert!(Projection::new(&input, &output).is_err());
}

#[test]
fn test_multi_project_happy_path() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");
    let inputs = vec![
        vec![x.clone(), y.clone()].into_boxed_slice(),
        vec![y.clone(), z.clone()].into_boxed_slice(),
    ];
    let output = vec![z, y, x];

    let projection = MultiProjection::new(&inputs, &output).expect("ok");
    assert_eq!(projection.inputs(), inputs);
    assert_eq!(projection.output(), output);

    assert_eq!(
        projection.apply(&[
            &[Variable::new(1), Variable::new(2)].into(),
            &[Variable::new(2), Variable::new(3)].into()
        ]),
        vec![Variable::new(3), Variable::new(2), Variable::new(1)].into()
    );
    assert_eq!(
        projection.from_pair(
            &[Variable::new(3), Variable::new(2)].into(),
            &[Variable::new(2), Variable::new(1)].into(),
        ),
        vec![Variable::new(1), Variable::new(2), Variable::new(3)].into()
    );
}

#[test]
fn test_multi_project_missing_variable() {
    let x = MetaVar::new("x");
    let y = MetaVar::new("y");
    let z = MetaVar::new("z");
    let inputs = vec![
        vec![x.clone(), y.clone()].into_boxed_slice(),
        vec![y.clone(), x.clone()].into_boxed_slice(),
    ];
    let output = vec![z, y, x];

    assert!(MultiProjection::new(&inputs, &output).is_err());
}
