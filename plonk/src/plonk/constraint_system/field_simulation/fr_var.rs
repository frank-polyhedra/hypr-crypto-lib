use crate::plonk::constraint_system::{field_simulation::SimFrMulVar, TurboCS, VarIndex};
use algebra::{
    cmp::{max, min},
    prelude::*,
};
use crypto::field_simulation::{SimFr, SimFrParams, SimReducibility};

/// `SimFrVar` is the variable for `SimFr` in
/// `TurboConstraintSystem<BLSScalar>`
#[derive(Clone)]
pub struct SimFrVar<F: Scalar, P: SimFrParams<F>> {
    /// the `SimFr` value.
    pub val: SimFr<F, P>,
    /// the `SimFr` variables.
    pub var: Vec<VarIndex>,
}

impl<F: Scalar, P: SimFrParams<F>> SimFrVar<F, P> {
    /// Create a zero `SimFr`.
    pub fn new(cs: &TurboCS<F>) -> Self {
        Self {
            val: SimFr::<F, P>::default(),
            var: vec![cs.zero_var(); P::NUM_OF_LIMBS],
        }
    }

    /// the Sub operation.
    pub fn sub(&self, cs: &mut TurboCS<F>, other: &SimFrVar<F, P>) -> SimFrVar<F, P> {
        let mut res = SimFrVar::<F, P>::new(cs);
        res.val = &self.val - &other.val;

        let zero = F::zero();
        let one = F::one();
        let minus_one = one.neg();

        let zero_var = cs.zero_var();

        let r_limbs = P::scalar_field_sub_pad_in_limbs();

        // The following gate represents
        // res.var[i] := self.var[i] - other.var[i] + r_limbs[i]
        for (i, r_limb) in r_limbs.iter().enumerate().take(P::NUM_OF_LIMBS) {
            res.var[i] = cs.new_variable(res.val.limbs[i]);

            cs.push_add_selectors(one, zero, minus_one, zero);
            cs.push_mul_selectors(zero, zero);
            cs.push_constant_selector(*r_limb);
            cs.push_ecc_selector(zero);
            cs.push_out_selector(one);

            cs.wiring[0].push(self.var[i]);
            cs.wiring[1].push(zero_var);
            cs.wiring[2].push(other.var[i]);
            cs.wiring[3].push(zero_var);
            cs.wiring[4].push(res.var[i]);
            cs.finish_new_gate();
        }

        res
    }

    /// the Mul operation.
    pub fn mul(&self, cs: &mut TurboCS<F>, other: &SimFrVar<F, P>) -> SimFrMulVar<F, P> {
        let mut res = SimFrMulVar::<F, P>::new(cs);
        res.val = &self.val * &other.val;

        let zero = F::zero();
        let one = F::one();

        let zero_var = cs.zero_var();

        for i in 0..P::NUM_OF_LIMBS_MUL {
            let smallest_left = max(P::NUM_OF_LIMBS, i + 1) - P::NUM_OF_LIMBS;
            let largest_left = min(i, P::NUM_OF_LIMBS - 1);

            let left_array = (smallest_left..=largest_left).collect::<Vec<_>>();

            let mut prior_res_val = F::zero();
            let mut prior_res = cs.zero_var();
            for left in left_array {
                let res_val =
                    prior_res_val.add(&self.val.limbs[left].mul(&other.val.limbs[i - left]));
                let res = cs.new_variable(res_val);

                // The following gate represents
                // res := prior_res + self.var[left] * other.var[i - left]

                cs.push_add_selectors(one, zero, zero, zero);
                cs.push_mul_selectors(zero, one);
                cs.push_constant_selector(zero);
                cs.push_ecc_selector(zero);
                cs.push_out_selector(one);

                cs.wiring[0].push(prior_res);
                cs.wiring[1].push(zero_var);
                cs.wiring[2].push(self.var[left]);
                cs.wiring[3].push(other.var[i - left]);
                cs.wiring[4].push(res);
                cs.finish_new_gate();

                prior_res = res;
                prior_res_val = res_val;
            }

            res.var[i] = prior_res;
        }
        res
    }

    /// Alloc a constant gate.
    pub fn alloc_constant(cs: &mut TurboCS<F>, val: &SimFr<F, P>) -> Self {
        let mut res = Self::new(cs);
        res.val = (*val).clone();
        for i in 0..P::NUM_OF_LIMBS {
            res.var[i] = cs.new_variable(val.limbs[i]);
            cs.insert_constant_gate(res.var[i], val.limbs[i]);
        }
        res
    }

    /// Alloc an input variable.
    pub fn alloc_input(cs: &mut TurboCS<F>, val: &SimFr<F, P>) -> Self {
        let mut res = Self::new(cs);
        res.val = (*val).clone();
        for i in 0..P::NUM_OF_LIMBS {
            res.var[i] = cs.new_variable(val.limbs[i]);
        }
        res
    }

    /// Alloc a witness variable and range check gate.
    pub fn alloc_witness(cs: &mut TurboCS<F>, val: &SimFr<F, P>) -> (Self, Vec<VarIndex>) {
        assert!(val.num_of_additions_over_normal_form == SimReducibility::StrictlyNotReducible);

        let mut res = Self::new(cs);
        res.val = (*val).clone();
        res.val.num_of_additions_over_normal_form = SimReducibility::AtMostReducibleByOne;

        let mut bits = Vec::new();

        for i in 0..P::NUM_OF_LIMBS {
            res.var[i] = cs.new_variable(val.limbs[i]);

            if i == P::NUM_OF_LIMBS - 1 {
                bits.extend_from_slice(&cs.range_check(res.var[i], P::BIT_IN_TOP_LIMB));
            } else {
                bits.extend_from_slice(&cs.range_check(res.var[i], P::BIT_PER_LIMB));
            }
        }
        (res, bits)
    }

    /// Alloc a witness variable and range check gate with bounded.
    pub fn alloc_witness_bounded_total_bits(
        cs: &mut TurboCS<F>,
        val: &SimFr<F, P>,
        total_bits: usize,
    ) -> (Self, Vec<VarIndex>) {
        assert!(val.num_of_additions_over_normal_form == SimReducibility::StrictlyNotReducible);

        let mut res = Self::new(cs);
        res.val = (*val).clone();
        if total_bits == 253 {
            res.val.num_of_additions_over_normal_form = SimReducibility::AtMostReducibleByOne;
        }

        let mut remaining_bits = total_bits;

        let mut bits = Vec::new();

        for i in 0..P::NUM_OF_LIMBS {
            if remaining_bits != 0 {
                res.var[i] = cs.new_variable(val.limbs[i]);
                let bit_limit = min(remaining_bits, P::BIT_PER_LIMB);
                bits.extend_from_slice(&cs.range_check(res.var[i], bit_limit));
                remaining_bits -= bit_limit;
            } else {
                res.var[i] = cs.zero_var();
            }
        }
        (res, bits)
    }
}

#[cfg(test)]
mod test_ristretto_bls12_381 {
    use crate::plonk::constraint_system::{
        field_simulation::{SimFrMulVar, SimFrVar},
        TurboCS,
    };
    use algebra::{bls12_381::BLSScalar, ops::Shl, prelude::*};
    use crypto::field_simulation::{SimFr, SimFrParams, SimFrParamsBLSRistretto};
    use num_bigint::{BigUint, RandBigInt};

    type SimFrTest = SimFr<BLSScalar, SimFrParamsBLSRistretto>;
    type SimFrVarTest = SimFrVar<BLSScalar, SimFrParamsBLSRistretto>;
    type SimFrMulVarTest = SimFrMulVar<BLSScalar, SimFrParamsBLSRistretto>;

    fn test_sim_fr_equality(cs: TurboCS<BLSScalar>, val: &SimFrVarTest) {
        let mut cs = cs;
        for i in 0..SimFrParamsBLSRistretto::NUM_OF_LIMBS {
            cs.insert_constant_gate(val.var[i], val.val.limbs[i]);
        }

        let witness = cs.get_and_clear_witness();
        assert!(cs.verify_witness(&witness[..], &[]).is_ok());
    }

    fn test_sim_fr_mul_equality(cs: TurboCS<BLSScalar>, val: &SimFrMulVarTest) {
        let mut cs = cs;
        for i in 0..SimFrParamsBLSRistretto::NUM_OF_LIMBS_MUL {
            cs.insert_constant_gate(val.var[i], val.val.limbs[i]);
        }

        let witness = cs.get_and_clear_witness();
        assert!(cs.verify_witness(&witness[..], &[]).is_ok());
    }

    #[test]
    fn test_alloc_constant() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBLSRistretto::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let a_sim_fr = SimFrTest::from(&a);

            {
                let mut cs = TurboCS::<BLSScalar>::new();
                let a_sim_fr_var = SimFrVarTest::alloc_constant(&mut cs, &a_sim_fr);
                test_sim_fr_equality(cs, &a_sim_fr_var);
            }
        }
    }

    #[test]
    fn test_alloc_witness() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBLSRistretto::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let a_sim_fr = SimFrTest::from(&a);

            {
                let mut cs = TurboCS::<BLSScalar>::new();
                let (a_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &a_sim_fr);
                test_sim_fr_equality(cs, &a_sim_fr_var);
            }
        }
    }

    #[test]
    fn test_sub() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBLSRistretto::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);

            let a_sim_fr = SimFrTest::from(&a);
            let b_sim_fr = SimFrTest::from(&b);

            {
                let mut cs = TurboCS::<BLSScalar>::new();

                let (a_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &a_sim_fr);
                let (b_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &b_sim_fr);

                let c_sim_fr_var = a_sim_fr_var.sub(&mut cs, &b_sim_fr_var);
                test_sim_fr_equality(cs, &c_sim_fr_var);
            }
        }
    }

    #[test]
    fn test_mul() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBLSRistretto::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);

            let a_sim_fr = SimFrTest::from(&a);
            let b_sim_fr = SimFrTest::from(&b);

            {
                let mut cs = TurboCS::<BLSScalar>::new();

                let (a_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &a_sim_fr);
                let (b_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &b_sim_fr);

                let c_sim_fr_mul_var = a_sim_fr_var.mul(&mut cs, &b_sim_fr_var);
                test_sim_fr_mul_equality(cs, &c_sim_fr_mul_var);
            }
        }
    }

    #[test]
    fn test_bounded_allocated_witness() {
        let mut prng = test_rng();

        for _ in 0..100 {
            let a = prng.gen_biguint(240);
            let a_sim_fr = SimFrTest::from(&a);

            {
                let mut cs = TurboCS::<BLSScalar>::new();

                let (a_sim_fr_var, _) =
                    SimFrVarTest::alloc_witness_bounded_total_bits(&mut cs, &a_sim_fr, 240);
                test_sim_fr_equality(cs, &a_sim_fr_var);
            }
        }
    }

    #[test]
    #[should_panic]
    fn test_bounded_allocated_witness_bad() {
        let a = BigUint::from(1u32).shl(240);
        let a_sim_fr = SimFrTest::from(&a);

        {
            let mut cs = TurboCS::<BLSScalar>::new();

            let (a_sim_fr_var, _) =
                SimFrVarTest::alloc_witness_bounded_total_bits(&mut cs, &a_sim_fr, 240);

            test_sim_fr_equality(cs, &a_sim_fr_var);
        }
    }
}

#[cfg(test)]
mod test_secq256k1_bls12_381 {
    use crate::plonk::constraint_system::{
        field_simulation::{SimFrMulVar, SimFrVar},
        TurboCS,
    };
    use algebra::{bls12_381::BLSScalar, ops::Shl, prelude::*};
    use crypto::field_simulation::{SimFr, SimFrParams, SimFrParamsBLSSecq256k1};
    use num_bigint::{BigUint, RandBigInt};

    type SimFrTest = SimFr<BLSScalar, SimFrParamsBLSSecq256k1>;
    type SimFrVarTest = SimFrVar<BLSScalar, SimFrParamsBLSSecq256k1>;
    type SimFrMulVarTest = SimFrMulVar<BLSScalar, SimFrParamsBLSSecq256k1>;

    fn test_sim_fr_equality(cs: TurboCS<BLSScalar>, val: &SimFrVarTest) {
        let mut cs = cs;
        for i in 0..SimFrParamsBLSSecq256k1::NUM_OF_LIMBS {
            cs.insert_constant_gate(val.var[i], val.val.limbs[i]);
        }

        let witness = cs.get_and_clear_witness();
        assert!(cs.verify_witness(&witness[..], &[]).is_ok());
    }

    fn test_sim_fr_mul_equality(cs: TurboCS<BLSScalar>, val: &SimFrMulVarTest) {
        let mut cs = cs;
        for i in 0..SimFrParamsBLSSecq256k1::NUM_OF_LIMBS_MUL {
            cs.insert_constant_gate(val.var[i], val.val.limbs[i]);
        }

        let witness = cs.get_and_clear_witness();
        assert!(cs.verify_witness(&witness[..], &[]).is_ok());
    }

    #[test]
    fn test_alloc_constant() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBLSSecq256k1::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let a_sim_fr = SimFrTest::from(&a);

            {
                let mut cs = TurboCS::<BLSScalar>::new();
                let a_sim_fr_var = SimFrVarTest::alloc_constant(&mut cs, &a_sim_fr);
                test_sim_fr_equality(cs, &a_sim_fr_var);
            }
        }
    }

    #[test]
    fn test_alloc_witness() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBLSSecq256k1::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let a_sim_fr = SimFrTest::from(&a);

            {
                let mut cs = TurboCS::<BLSScalar>::new();
                let (a_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &a_sim_fr);
                test_sim_fr_equality(cs, &a_sim_fr_var);
            }
        }
    }

    #[test]
    fn test_sub() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBLSSecq256k1::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);

            let a_sim_fr = SimFrTest::from(&a);
            let b_sim_fr = SimFrTest::from(&b);

            {
                let mut cs = TurboCS::<BLSScalar>::new();

                let (a_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &a_sim_fr);
                let (b_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &b_sim_fr);

                let c_sim_fr_var = a_sim_fr_var.sub(&mut cs, &b_sim_fr_var);
                test_sim_fr_equality(cs, &c_sim_fr_var);
            }
        }
    }

    #[test]
    fn test_mul() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBLSSecq256k1::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);

            let a_sim_fr = SimFrTest::from(&a);
            let b_sim_fr = SimFrTest::from(&b);

            {
                let mut cs = TurboCS::<BLSScalar>::new();

                let (a_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &a_sim_fr);
                let (b_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &b_sim_fr);

                let c_sim_fr_mul_var = a_sim_fr_var.mul(&mut cs, &b_sim_fr_var);
                test_sim_fr_mul_equality(cs, &c_sim_fr_mul_var);
            }
        }
    }

    #[test]
    fn test_bounded_allocated_witness() {
        let mut prng = test_rng();

        for _ in 0..100 {
            let a = prng.gen_biguint(240);
            let a_sim_fr = SimFrTest::from(&a);

            {
                let mut cs = TurboCS::<BLSScalar>::new();

                let (a_sim_fr_var, _) =
                    SimFrVarTest::alloc_witness_bounded_total_bits(&mut cs, &a_sim_fr, 240);
                test_sim_fr_equality(cs, &a_sim_fr_var);
            }
        }
    }

    #[test]
    #[should_panic]
    fn test_bounded_allocated_witness_bad() {
        let a = BigUint::from(1u32).shl(240);
        let a_sim_fr = SimFrTest::from(&a);

        {
            let mut cs = TurboCS::<BLSScalar>::new();

            let (a_sim_fr_var, _) =
                SimFrVarTest::alloc_witness_bounded_total_bits(&mut cs, &a_sim_fr, 240);

            test_sim_fr_equality(cs, &a_sim_fr_var);
        }
    }
}

#[cfg(test)]
mod test_ristretto_bn254 {
    use crate::plonk::constraint_system::{
        field_simulation::{SimFrMulVar, SimFrVar},
        TurboCS,
    };
    use algebra::{bn254::BN254Scalar, ops::Shl, prelude::*};
    use crypto::field_simulation::{SimFr, SimFrParams, SimFrParamsBN254Ristretto};
    use num_bigint::{BigUint, RandBigInt};

    type SimFrTest = SimFr<BN254Scalar, SimFrParamsBN254Ristretto>;
    type SimFrVarTest = SimFrVar<BN254Scalar, SimFrParamsBN254Ristretto>;
    type SimFrMulVarTest = SimFrMulVar<BN254Scalar, SimFrParamsBN254Ristretto>;

    fn test_sim_fr_equality(cs: TurboCS<BN254Scalar>, val: &SimFrVarTest) {
        let mut cs = cs;
        for i in 0..SimFrParamsBN254Ristretto::NUM_OF_LIMBS {
            cs.insert_constant_gate(val.var[i], val.val.limbs[i]);
        }

        let witness = cs.get_and_clear_witness();
        assert!(cs.verify_witness(&witness[..], &[]).is_ok());
    }

    fn test_sim_fr_mul_equality(cs: TurboCS<BN254Scalar>, val: &SimFrMulVarTest) {
        let mut cs = cs;
        for i in 0..SimFrParamsBN254Ristretto::NUM_OF_LIMBS_MUL {
            cs.insert_constant_gate(val.var[i], val.val.limbs[i]);
        }

        let witness = cs.get_and_clear_witness();
        assert!(cs.verify_witness(&witness[..], &[]).is_ok());
    }

    #[test]
    fn test_alloc_constant() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBN254Ristretto::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let a_sim_fr = SimFrTest::from(&a);

            {
                let mut cs = TurboCS::<BN254Scalar>::new();
                let a_sim_fr_var = SimFrVarTest::alloc_constant(&mut cs, &a_sim_fr);
                test_sim_fr_equality(cs, &a_sim_fr_var);
            }
        }
    }

    #[test]
    fn test_alloc_witness() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBN254Ristretto::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let a_sim_fr = SimFrTest::from(&a);

            {
                let mut cs = TurboCS::<BN254Scalar>::new();
                let (a_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &a_sim_fr);
                test_sim_fr_equality(cs, &a_sim_fr_var);
            }
        }
    }

    #[test]
    fn test_sub() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBN254Ristretto::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);

            let a_sim_fr = SimFrTest::from(&a);
            let b_sim_fr = SimFrTest::from(&b);

            {
                let mut cs = TurboCS::<BN254Scalar>::new();

                let (a_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &a_sim_fr);
                let (b_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &b_sim_fr);

                let c_sim_fr_var = a_sim_fr_var.sub(&mut cs, &b_sim_fr_var);
                test_sim_fr_equality(cs, &c_sim_fr_var);
            }
        }
    }

    #[test]
    fn test_mul() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBN254Ristretto::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);

            let a_sim_fr = SimFrTest::from(&a);
            let b_sim_fr = SimFrTest::from(&b);

            {
                let mut cs = TurboCS::<BN254Scalar>::new();

                let (a_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &a_sim_fr);
                let (b_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &b_sim_fr);

                let c_sim_fr_mul_var = a_sim_fr_var.mul(&mut cs, &b_sim_fr_var);
                test_sim_fr_mul_equality(cs, &c_sim_fr_mul_var);
            }
        }
    }

    #[test]
    fn test_bounded_allocated_witness() {
        let mut prng = test_rng();

        for _ in 0..100 {
            let a = prng.gen_biguint(240);
            let a_sim_fr = SimFrTest::from(&a);

            {
                let mut cs = TurboCS::<BN254Scalar>::new();

                let (a_sim_fr_var, _) =
                    SimFrVarTest::alloc_witness_bounded_total_bits(&mut cs, &a_sim_fr, 240);
                test_sim_fr_equality(cs, &a_sim_fr_var);
            }
        }
    }

    #[test]
    #[should_panic]
    fn test_bounded_allocated_witness_bad() {
        let a = BigUint::from(1u32).shl(240);
        let a_sim_fr = SimFrTest::from(&a);

        {
            let mut cs = TurboCS::<BN254Scalar>::new();

            let (a_sim_fr_var, _) =
                SimFrVarTest::alloc_witness_bounded_total_bits(&mut cs, &a_sim_fr, 240);

            test_sim_fr_equality(cs, &a_sim_fr_var);
        }
    }
}

#[cfg(test)]
mod test_secq256k1_bn254 {
    use crate::plonk::constraint_system::{
        field_simulation::{SimFrMulVar, SimFrVar},
        TurboCS,
    };
    use algebra::{bn254::BN254Scalar, ops::Shl, prelude::*};
    use crypto::field_simulation::{SimFr, SimFrParams, SimFrParamsBN254Secq256k1};
    use num_bigint::{BigUint, RandBigInt};

    type SimFrTest = SimFr<BN254Scalar, SimFrParamsBN254Secq256k1>;
    type SimFrVarTest = SimFrVar<BN254Scalar, SimFrParamsBN254Secq256k1>;
    type SimFrMulVarTest = SimFrMulVar<BN254Scalar, SimFrParamsBN254Secq256k1>;

    fn test_sim_fr_equality(cs: TurboCS<BN254Scalar>, val: &SimFrVarTest) {
        let mut cs = cs;
        for i in 0..SimFrParamsBN254Secq256k1::NUM_OF_LIMBS {
            cs.insert_constant_gate(val.var[i], val.val.limbs[i]);
        }

        let witness = cs.get_and_clear_witness();
        assert!(cs.verify_witness(&witness[..], &[]).is_ok());
    }

    fn test_sim_fr_mul_equality(cs: TurboCS<BN254Scalar>, val: &SimFrMulVarTest) {
        let mut cs = cs;
        for i in 0..SimFrParamsBN254Secq256k1::NUM_OF_LIMBS_MUL {
            cs.insert_constant_gate(val.var[i], val.val.limbs[i]);
        }

        let witness = cs.get_and_clear_witness();
        assert!(cs.verify_witness(&witness[..], &[]).is_ok());
    }

    #[test]
    fn test_alloc_constant() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBN254Secq256k1::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let a_sim_fr = SimFrTest::from(&a);

            {
                let mut cs = TurboCS::<BN254Scalar>::new();
                let a_sim_fr_var = SimFrVarTest::alloc_constant(&mut cs, &a_sim_fr);
                test_sim_fr_equality(cs, &a_sim_fr_var);
            }
        }
    }

    #[test]
    fn test_alloc_witness() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBN254Secq256k1::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let a_sim_fr = SimFrTest::from(&a);

            {
                let mut cs = TurboCS::<BN254Scalar>::new();
                let (a_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &a_sim_fr);
                test_sim_fr_equality(cs, &a_sim_fr_var);
            }
        }
    }

    #[test]
    fn test_sub() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBN254Secq256k1::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);

            let a_sim_fr = SimFrTest::from(&a);
            let b_sim_fr = SimFrTest::from(&b);

            {
                let mut cs = TurboCS::<BN254Scalar>::new();

                let (a_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &a_sim_fr);
                let (b_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &b_sim_fr);

                let c_sim_fr_var = a_sim_fr_var.sub(&mut cs, &b_sim_fr_var);
                test_sim_fr_equality(cs, &c_sim_fr_var);
            }
        }
    }

    #[test]
    fn test_mul() {
        let mut prng = test_rng();
        let p_biguint = SimFrParamsBN254Secq256k1::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &p_biguint);

            let a_sim_fr = SimFrTest::from(&a);
            let b_sim_fr = SimFrTest::from(&b);

            {
                let mut cs = TurboCS::<BN254Scalar>::new();

                let (a_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &a_sim_fr);
                let (b_sim_fr_var, _) = SimFrVarTest::alloc_witness(&mut cs, &b_sim_fr);

                let c_sim_fr_mul_var = a_sim_fr_var.mul(&mut cs, &b_sim_fr_var);
                test_sim_fr_mul_equality(cs, &c_sim_fr_mul_var);
            }
        }
    }

    #[test]
    fn test_bounded_allocated_witness() {
        let mut prng = test_rng();

        for _ in 0..100 {
            let a = prng.gen_biguint(240);
            let a_sim_fr = SimFrTest::from(&a);

            {
                let mut cs = TurboCS::<BN254Scalar>::new();

                let (a_sim_fr_var, _) =
                    SimFrVarTest::alloc_witness_bounded_total_bits(&mut cs, &a_sim_fr, 240);
                test_sim_fr_equality(cs, &a_sim_fr_var);
            }
        }
    }

    #[test]
    #[should_panic]
    fn test_bounded_allocated_witness_bad() {
        let a = BigUint::from(1u32).shl(240);
        let a_sim_fr = SimFrTest::from(&a);

        {
            let mut cs = TurboCS::<BN254Scalar>::new();

            let (a_sim_fr_var, _) =
                SimFrVarTest::alloc_witness_bounded_total_bits(&mut cs, &a_sim_fr, 240);

            test_sim_fr_equality(cs, &a_sim_fr_var);
        }
    }
}
