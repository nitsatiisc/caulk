use ark_ff::{BigInteger, PrimeField};
use crate::plonk::{Component, Protoboard, Variable};

pub struct RangeCheckComponent {
    pub inputs: Vec<Variable>,
    pub outputs: Vec<Variable>,
    pub inputs_bits: Vec<Vec<Variable>>,
    pub intermediate: Vec<Vec<Variable>>,
    pub nbits: usize,
}

pub struct InnerProductComponent {
    pub input_xvec: Vec<Variable>,
    pub input_yvec: Vec<Variable>,
    pub output: Variable,
    pub z: Vec<Variable>,
    pub Z: Vec<Variable>,
    pub n: usize,

}

impl RangeCheckComponent {
    pub fn new(nbits: usize) -> Self {
        RangeCheckComponent {
            inputs: vec![],
            outputs: vec![],
            inputs_bits: vec![],
            intermediate: vec![],
            nbits,
        }
    }
}

impl InnerProductComponent {
    pub fn new(n: usize) -> Self {
        InnerProductComponent {
            input_xvec: vec![],
            input_yvec: vec![],
            output: Variable {name: "".to_string(), pb_index: 0 },
            z: vec![],
            Z: vec![],
            n,
        }
    }
}

impl<F:PrimeField> Component<F> for RangeCheckComponent {
    fn attach(&mut self, pb:&mut Protoboard<F>, inputs: &Vec<Variable>, outputs: &Vec<Variable>) {
        self.inputs = inputs.clone();
        self.outputs = outputs.clone();

        // allocate variables for input bits on the protoboard
        for i in 0..self.inputs.len() {
            let mut input_bits: Vec<Variable> = Vec::new();
            let mut intermediate_vec: Vec<Variable> = Vec::new();
            for j in 0..self.nbits {
                input_bits.push(Variable::new(""));
                intermediate_vec.push(Variable::new(""));
            }
            self.inputs_bits.push(input_bits);
            self.intermediate.push(intermediate_vec);
        }

        // assign the bits on the protoboard
        for i in 0..self.inputs.len() {
            for j in 0..self.nbits {
                pb.assign_index(&mut self.inputs_bits[i][j])
            }
        }

        // assign intermediate sums on the protoboard
        for i in 0..self.inputs.len() {
            for j in 0..self.nbits {
                pb.assign_index(&mut self.intermediate[i][j])
            }
        }
    }

    fn generate_constraints(&mut self, pb:&mut Protoboard<F>) {
        let minus_one = F::zero() - F::one();
        for i in 0..self.inputs.len() {
            for j in 0..self.nbits {
                pb.add_boolean_gate(&self.inputs_bits[i][j]);
            }
        }
        // enforce the reconstruction constraints:
        // inputs[i] = 2^0 input_bits[i][0] + ... + 2^{nbits - 1} input_bits[i][nbits - 1]
        // intermediate[i][0] = input_bits[i][nbits - 1]
        // intermediate[i][j] = 2*intermediate[j-1] + input_bits[nbits - 1 - j]
        // intermediate[i][nbits - 1] = inputs[i]
        for i in 0..self.inputs.len() {
            pb.add_addition_gate(&self.inputs_bits[i][self.nbits-1], &self.inputs_bits[i][self.nbits-1], &self.intermediate[i][0], F::one(), F::zero(), F::zero());
            pb.add_addition_gate(&self.inputs[i], &self.inputs[i], &self.intermediate[i][self.nbits-1], F::one(), F::zero(), F::zero());

            for j in 1..self.nbits {
                pb.add_addition_gate(&self.intermediate[i][j-1], &self.inputs_bits[i][self.nbits - j - 1], &self.intermediate[i][j], F::from(2u128), F::one(), F::zero());
            }
        }
    }

    fn generate_witness(&mut self, pb:&mut Protoboard<F>) {
        for i in 0..self.inputs.len() {
            let bits = pb.val(&self.inputs[i]).into_repr().to_bits_le();
            let bits = bits.iter().map(|x| F::from(*x as u128)).collect::<Vec<_>>();
            // Below, assumes that bits.len() >= self.nbits
            for j in 0..self.nbits {
                pb.assign_val(&self.inputs_bits[i][j], bits[j]);
            }

        }

        // assign values to intermediates
        for i in 0..self.inputs.len() {
            pb.assign_val(&self.intermediate[i][0], pb.val(&self.inputs_bits[i][self.nbits -1]));
            for j in 1..self.nbits {
                pb.assign_val(&self.intermediate[i][j], F::from(2u128)*pb.val(&self.intermediate[i][j-1]) + pb.val(&self.inputs_bits[i][self.nbits - j -1]));
            }
        }

    }
}

impl<F: PrimeField> Component<F> for InnerProductComponent {
    fn attach(&mut self, pb: &mut Protoboard<F>, inputs: &Vec<Variable>, outputs: &Vec<Variable>) {
        self.input_xvec = inputs[0..self.n].to_vec().clone();
        self.input_yvec = inputs[self.n..(2*self.n)].to_vec().clone();
        self.output = outputs[0].clone();

        // declare and assign intermediate variables on the protoboard
        let zero_var: Variable = Variable { name: "zero".to_string(), pb_index: 0};
        self.z = Vec::new();
        self.Z = Vec::new();
        self.z.resize(self.n, zero_var.clone());
        self.Z.resize(self.n, zero_var.clone());

        for i in 0..self.n {
            pb.assign_index(&mut self.z[i]);
            pb.assign_index(&mut self.Z[i]);
        }
    }

    fn generate_constraints(&mut self, pb: &mut Protoboard<F>) {
        // add multiplication gates first
        for i in 0..self.n {
            pb.add_multiplication_gate(&self.input_xvec[i], &self.input_yvec[i], &self.z[i]);
        }

        // add addition gates
        for i in 0..self.n-1 {
            pb.add_addition_gate(&self.z[i], &self.Z[i], &self.Z[i+1], F::one(), F::one(), F::zero());
        }

        pb.add_addition_gate(&self.z[self.n - 1], &self.Z[self.n - 1], &self.output, F::one(), F::one(), F::zero());
        pb.add_addition_gate(&self.Z[0], &self.Z[0], &self.Z[0], F::zero(), F::zero(), F::zero());

    }

    fn generate_witness(&mut self, pb: &mut Protoboard<F>) {
        // first assign values to the outputs of multiplication gates
        for i in 0..self.n {
            pb.assign_val(&self.z[i], pb.val(&self.input_xvec[i]) * pb.val(&self.input_yvec[i]));
        }
        // set Z[0] = 0
        pb.assign_val(&self.Z[0], F::zero());
        // assign values to Z[1],..Z[n-1]
        for i in 1..self.n {
            pb.assign_val(&self.Z[i], pb.val(&self.Z[i - 1]) + pb.val(&self.z[i - 1]));
        }
        pb.assign_val(&self.output, pb.val(&self.Z[self.n-1]) + pb.val(&self.z[self.n-1]));
    }
}
