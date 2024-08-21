// This module implements plonk circuits, prover and verifier.

pub mod gadgets;

use ark_ff::{BigInteger, PrimeField};

#[derive(Clone, Debug)]
pub struct Variable {
    pub name: String,
    pub pb_index: usize,
}

impl Variable {

    pub fn new(name: &str) -> Self {
        Variable {
            name: name.to_string(),
            pb_index: usize::MAX
        }
    }
}

// Defines the plonk constraint
// q_m(x[a]x[b]) + q_l x[a] + q_r x[b] + q_o x[c] + q_c = 0
#[derive(Clone, Debug)]
pub struct Constraint<F: PrimeField> {
    pub q_m: F,
    pub q_l: F,
    pub q_r: F,
    pub q_o: F,
    pub q_c: F,
    pub idx_a: usize,
    pub idx_b: usize,
    pub idx_c: usize
}

#[derive(Clone, Debug)]
pub struct ConstraintSystem<F: PrimeField> {
    pub constraints: Vec<Constraint<F>>,
}

// Defines a component/gadget.
// input: a set of assigned variables on protoboard
// output: a set of assigned variables on protoboard
pub trait Component<F: PrimeField> {
    fn attach(&mut self, pb:&mut Protoboard<F>, inputs: &Vec<Variable>, outputs: &Vec<Variable>);
    fn generate_constraints(&mut self, pb:&mut Protoboard<F>);
    fn generate_witness(&mut self, pb:&mut Protoboard<F>);
}



pub struct Protoboard<F: PrimeField> {
    pub n_variables: usize,
    pub n_inputs: usize,
    pub permutation: Vec<usize>,
    pub pb_vals: Vec<F>,
    pub cs: ConstraintSystem<F>,
}

impl<F:PrimeField> Protoboard<F> {
    pub fn new() -> Self {
        Protoboard::<F> {
            n_variables: 0,
            n_inputs: 0,
            permutation: vec![],
            pb_vals: vec![],
            cs: ConstraintSystem::<F> { constraints: vec![] },
        }
    }

    pub fn get_input_size(&self) -> usize {
        self.n_inputs
    }

    pub fn get_num_constraints(&self) -> usize {
        self.cs.constraints.len()
    }

    pub fn get_num_variables(&self) -> usize {
        self.n_variables
    }

    pub fn assign_index(&mut self, var: &mut Variable) {
        var.pb_index = self.n_variables;
        self.pb_vals.push(F::zero());
        self.n_variables = self.n_variables+1;
    }

    pub fn assign_val(&mut self, var:&Variable, val: F) {
        self.pb_vals[var.pb_index] = val;
    }

    pub fn val(&self, var:&Variable) -> F {
        self.pb_vals[var.pb_index]
    }

    pub fn add_constraint(&mut self, constraint: &Constraint<F>) {
        let constraint: Constraint<F> = (*constraint).clone();
        assert_eq!(constraint.idx_a < self.n_variables, true, "Left variable {} un-assigned", constraint.idx_a);
        assert_eq!(constraint.idx_b < self.n_variables, true, "Right variable {} un-assigned", constraint.idx_b);
        assert_eq!(constraint.idx_c < self.n_variables, true, "Output variable {} un-assigned", constraint.idx_c);
        self.cs.constraints.push(constraint.clone());
    }

    // add gate such that out = a.left + b.right + c
    pub fn add_addition_gate(&mut self, left: &Variable, right: &Variable, out: &Variable, a: F, b: F, c: F) {
        let constraint: Constraint<F> = Constraint {
            q_m: F::zero(),
            q_l: a,
            q_r: b,
            q_o: F::zero().sub(F::one()),
            q_c: c,
            idx_a: left.pb_index,
            idx_b: right.pb_index,
            idx_c: out.pb_index
        };

        self.add_constraint(&constraint);
    }

    // add gate such that out = left * right
    pub fn add_multiplication_gate(&mut self, left: &Variable, right: &Variable, out: &Variable) {
        let constraint: Constraint<F> = Constraint {
            q_m: F::one(),
            q_l: F::zero(),
            q_r: F::zero(),
            q_o: F::zero() - F::one(),
            q_c: F::zero(),
            idx_a: left.pb_index,
            idx_b: right.pb_index,
            idx_c: out.pb_index
        };

        self.add_constraint(&constraint);
    }

    // add gate such that left = left * right
    pub fn add_boolean_gate(&mut self, left: &Variable) {
        let constraint: Constraint<F> = Constraint {
            q_m: F::one(),
            q_l: F::zero() - F::one(),
            q_r: F::zero(),
            q_o: F::zero(),
            q_c: F::zero(),
            idx_a: left.pb_index,
            idx_b: left.pb_index,
            idx_c: left.pb_index
        };

        self.add_constraint(&constraint);
    }

    pub fn add_public_input(&mut self, left: &Variable) {
        let constraint: Constraint<F> = Constraint {
            q_m: F::zero(),
            q_l: F::one(),
            q_r: F::zero(),
            q_o: F::zero(),
            q_c: F::zero(),
            idx_a: left.pb_index,
            idx_b: left.pb_index,
            idx_c: left.pb_index
        };
        self.add_constraint(&constraint);

    }

    pub fn is_satisfied(&mut self) ->bool {
        for i in 0..self.cs.constraints.len() {
            let constraint: Constraint<F> = self.cs.constraints[i].clone();
            let q_m = constraint.q_m;
            let q_l = constraint.q_l;
            let q_r = constraint.q_r;
            let q_o = constraint.q_o;
            let q_c = constraint.q_c;

            let sum:F = q_m * self.pb_vals[constraint.idx_a] * self.pb_vals[constraint.idx_b] + q_l * self.pb_vals[constraint.idx_a]
                        + q_r * self.pb_vals[constraint.idx_b] + q_o * self.pb_vals[constraint.idx_c] + q_c;
            if sum != F::zero() {
                println!("Constraint {} with {:?} not satisfied", i, constraint);
                return false;
            }

        }
        true
    }
}

mod tests {
    use ark_bls12_381::Bls12_381;
    use ark_ec::bls12::Bls12;
    use ark_ec::PairingEngine;
    use ark_ff::{One, Zero};
    use crate::plonk::gadgets::{InnerProductComponent, RangeCheckComponent};
    use super::*;

    #[test]
    pub fn test_simple_satisfiability()
    {
        test_simple_satisfiability_helper::<Bls12_381>();
    }

    #[test]
    pub fn test_range_component()
    {
        test_range_component_helper::<Bls12_381>();
    }

    #[test]
    pub fn test_inner_product_component()
    {
        test_inner_product_helper::<<Bls12<ark_bls12_381::Parameters> as ark_ec::PairingEngine>::Fr>();
    }

    fn test_range_component_helper<E: PairingEngine>() {
        let mut pb: Protoboard<E::Fr> = Protoboard::new();
        let mut range_checker: RangeCheckComponent = RangeCheckComponent::new(5usize);
        let n_inputs: usize = 2;
        let mut inputs: Vec<Variable> = Vec::new();
        for i in 0..n_inputs {
            inputs.push(Variable::new("input"));
        }

        for i in 0..inputs.len() {
            pb.assign_index(&mut inputs[i]);
        }

        range_checker.attach(&mut pb, &inputs, &inputs);
        range_checker.generate_constraints(&mut pb);

        // assign values to inputs
        for i in 0..inputs.len() {
            pb.assign_val(&inputs[i], E::Fr::from(11u128));
        }
        range_checker.generate_witness(&mut pb);

        // Print Variables and Check circuit satisfiability
        for i in 0..pb.pb_vals.len() {
            println!("Value of variable {} = {}", i, pb.pb_vals[i]);
        }

        println!("Circuit Satisfied = {}", pb.is_satisfied());

    }

    fn test_inner_product_helper<F: PrimeField>() {
        let mut pb: Protoboard<F> = Protoboard::new();
        let n: usize = 10;
        let zero_var: Variable = Variable {name: "zero".to_string(), pb_index: 0};
        let mut inner_product: InnerProductComponent = InnerProductComponent::new(n);

        let x_vals: Vec<u128> = vec![0,1,2,3,4,5,6,7,8,9];
        let y_vals: Vec<u128> = vec![1,1,1,1,1,1,1,1,1,1];

        // declare variables on protoboard
        let mut input: Vec<Variable> = Vec::new(); input.resize(2*n, zero_var.clone());
        let mut output = zero_var.clone();

        for i in 0..2*n {
            pb.assign_index(&mut input[i]);
        }

        pb.assign_index(&mut output);

        // Attach the inner product gadget
        inner_product.attach(&mut pb, &input, &vec![output.clone()]);
        inner_product.generate_constraints(&mut pb);

        // Generate witness
        for i in 0..n {
            pb.assign_val(&input[i], F::from(x_vals[i]));
            pb.assign_val(&input[i+n], F::from(y_vals[i]));
        }
        inner_product.generate_witness(&mut pb);

        // Print Variables and Check circuit satisfiability
        for i in 0..pb.pb_vals.len() {
            println!("Value of variable {} = {}", i, pb.pb_vals[i]);
        }
        println!("Circuit Satisfied = {}", pb.is_satisfied());
    }

    fn test_simple_satisfiability_helper<E: PairingEngine>()
    {
        let mut pb: Protoboard<E::Fr> = Protoboard::new();

        // Encode the following circuit:
        // Inputs: x, y, z
        // Output: w
        // sq_x = x*x, sq_y = y*y, sq_z = z*z,
        // c_xy = x*y, c_yz = y*z, c_zx = z*x
        // sum_cross_1 = 2*c_xy + 2*c_yz
        // sum_cross = sum_cross_1 + 2*c_zx
        // sum_square_1 = sq_x + sq_y
        // sum_square = sum_square_1 + sq_z
        // w = sum_square + sum_cross

        let mut x: Variable = Variable::new("x");
        let mut y: Variable = Variable::new("y");
        let mut z: Variable = Variable::new("z");
        let mut w: Variable = Variable::new("w");

        // Internal variables
        let mut sq_x: Variable = Variable::new("");
        let mut sq_y: Variable = Variable::new("");
        let mut sq_z: Variable = Variable::new("");
        let mut c_xy: Variable = Variable::new("");
        let mut c_yz: Variable = Variable::new("");
        let mut c_zx: Variable = Variable::new("");
        let mut sum_cross_1: Variable = Variable::new("");
        let mut sum_square_1: Variable = Variable::new("");
        let mut sum_cross: Variable = Variable::new("");
        let mut sum_square: Variable = Variable::new("");

        // Assign variables
        pb.assign_index(&mut x);
        pb.assign_index(&mut y);
        pb.assign_index(&mut z);
        pb.assign_index(&mut w);
        pb.assign_index(&mut sq_x);
        pb.assign_index(&mut sq_y);
        pb.assign_index(&mut sq_z);
        pb.assign_index(&mut c_xy);
        pb.assign_index(&mut c_yz);
        pb.assign_index(&mut c_zx);
        pb.assign_index(&mut sum_cross_1);
        pb.assign_index(&mut sum_square_1);
        pb.assign_index(&mut sum_cross);
        pb.assign_index(&mut sum_square);

        // Generate constraints
        pb.add_multiplication_gate(&x, &x, &sq_x);
        pb.add_multiplication_gate(&y, &y, &sq_y);
        pb.add_multiplication_gate(&z, &z, &sq_z);
        pb.add_multiplication_gate(&x, &y, &c_xy);
        pb.add_multiplication_gate(&y, &z, &c_yz);
        pb.add_multiplication_gate(&z, &x, &c_zx);
        pb.add_addition_gate(&c_xy, &c_yz, &sum_cross_1, E::Fr::from(2u128), E::Fr::from(2u128), E::Fr::zero());
        pb.add_addition_gate(&c_zx, &sum_cross_1, &sum_cross, E::Fr::from(2u128), E::Fr::one(), E::Fr::zero());
        pb.add_addition_gate(&sq_x, &sq_y, &sum_square_1, E::Fr::one(), E::Fr::one(), E::Fr::zero());
        pb.add_addition_gate(&sq_z, &sum_square_1, &sum_square, E::Fr::one(), E::Fr::one(), E::Fr::zero());
        pb.add_addition_gate(&sum_cross, &sum_square, &w, E::Fr::one(), E::Fr::one(), E::Fr::zero());



        // Assign values
        pb.assign_val(&x, E::Fr::from(5u128));
        pb.assign_val(&y, E::Fr::from(3u128));
        pb.assign_val(&z, E::Fr::from(2u128));
        pb.assign_val(&c_xy, pb.val(&x) * pb.val(&y));
        pb.assign_val(&c_yz, pb.val(&y)*pb.val(&z));
        pb.assign_val(&c_zx, pb.val(&z) * pb.val(&x));
        pb.assign_val(&sq_x, pb.val(&x) * pb.val(&x));
        pb.assign_val(&sq_y, pb.val(&y) * pb.val(&y));
        pb.assign_val(&sq_z, pb.val(&z) * pb.val(&z));
        pb.assign_val(&sum_cross_1, pb.val(&c_xy) + pb.val(&c_xy) + pb.val(&c_yz) + pb.val(&c_yz));
        pb.assign_val(&sum_cross, pb.val(&sum_cross_1) + pb.val(&c_zx) + pb.val(&c_zx));
        pb.assign_val(&sum_square_1, pb.val(&sq_x) + pb.val(&sq_y));
        pb.assign_val(&sum_square, pb.val(&sum_square_1) + pb.val(&sq_z));
        pb.assign_val(&w, pb.val(&sum_square) + pb.val(&sum_cross));

        println!("The value of output w is {}", pb.val(&w).to_string());
        println!("Circuit satisfied {}", pb.is_satisfied());
    }



}


