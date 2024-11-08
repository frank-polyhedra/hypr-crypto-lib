use crate::field_simulation::SimFrParams;
use algebra::bls12_381::BLSScalar;
use core::str::FromStr;
use num_bigint::BigUint;

/// The parameters for field simulation for Ristretto.
#[derive(Clone, Default, Eq, PartialEq, Debug)]
pub struct SimFrParamsBLSRistretto;

impl SimFrParams<BLSScalar> for SimFrParamsBLSRistretto {
    const NUM_OF_LIMBS: usize = 6;
    const BIT_PER_LIMB: usize = 43;
    const BIT_IN_TOP_LIMB: usize = 38;
    const NUM_OF_GROUPS: usize = 6;

    fn scalar_field_in_biguint() -> BigUint {
        BigUint::from_str(
            "7237005577332262213973186563042994240857116359379907606001950938285454250989",
        )
        .unwrap()
    }

    fn scalar_field_in_limbs() -> Vec<BLSScalar> {
        [
            BLSScalar::from_str("3411763647469").unwrap(),
            BLSScalar::from_str("7643343815244").unwrap(),
            BLSScalar::from_str("358561053323").unwrap(),
            BLSScalar::from_str("0").unwrap(),
            BLSScalar::from_str("0").unwrap(),
            BLSScalar::from_str("137438953472").unwrap(),
        ]
        .to_vec()
    }

    fn scalar_field_sub_pad_in_limbs() -> Vec<BLSScalar> {
        [
            BLSScalar::from_str("10235290942407").unwrap(),
            BLSScalar::from_str("14133938423524").unwrap(),
            BLSScalar::from_str("9871776182178").unwrap(),
            BLSScalar::from_str("17592186044415").unwrap(),
            BLSScalar::from_str("17592186044414").unwrap(),
            BLSScalar::from_str("412316860414").unwrap(),
        ]
        .to_vec()
    }

    fn scalar_field_sub_pad_in_biguint() -> BigUint {
        BigUint::from_str(
            "21711016731996786641919559689128982722571349078139722818005852814856362752967",
        )
        .unwrap()
    }
}

/// The parameters for field simulation for the secq256k1 scalar field.
#[derive(Clone, Default, Eq, PartialEq, Debug)]
pub struct SimFrParamsBLSSecq256k1;

impl SimFrParams<BLSScalar> for SimFrParamsBLSSecq256k1 {
    const NUM_OF_LIMBS: usize = 6;
    const BIT_PER_LIMB: usize = 44;
    const BIT_IN_TOP_LIMB: usize = 36;
    const NUM_OF_GROUPS: usize = 6;

    fn scalar_field_in_biguint() -> BigUint {
        BigUint::from_str(
            "115792089237316195423570985008687907853269984665640564039457584007908834671663",
        )
        .unwrap()
    }

    fn scalar_field_in_limbs() -> Vec<BLSScalar> {
        [
            BLSScalar::from_str("17587891076143").unwrap(),
            BLSScalar::from_str("17592186044415").unwrap(),
            BLSScalar::from_str("17592186044415").unwrap(),
            BLSScalar::from_str("17592186044415").unwrap(),
            BLSScalar::from_str("17592186044415").unwrap(),
            BLSScalar::from_str("68719476735").unwrap(),
        ]
        .to_vec()
    }

    fn scalar_field_sub_pad_in_limbs() -> Vec<BLSScalar> {
        [
            BLSScalar::from_str("35175782152286").unwrap(),
            BLSScalar::from_str("35184372088830").unwrap(),
            BLSScalar::from_str("35184372088830").unwrap(),
            BLSScalar::from_str("35184372088830").unwrap(),
            BLSScalar::from_str("35184372088830").unwrap(),
            BLSScalar::from_str("137438953470").unwrap(),
        ]
        .to_vec()
    }

    fn scalar_field_sub_pad_in_biguint() -> BigUint {
        BigUint::from_str(
            "231584178474632390847141970017375815706539969331281128078915168015817669343326",
        )
        .unwrap()
    }
}

/// The parameters for field simulation for the zorro scalar field.
#[derive(Clone, Default, Eq, PartialEq, Debug)]
pub struct SimFrParamsBLSZorro;

impl SimFrParams<BLSScalar> for SimFrParamsBLSZorro {
    const NUM_OF_LIMBS: usize = 6;
    const BIT_PER_LIMB: usize = 44;
    const BIT_IN_TOP_LIMB: usize = 36;
    const NUM_OF_GROUPS: usize = 6;

    fn scalar_field_in_biguint() -> BigUint {
        BigUint::from_str(
            "57896044618658097711785492504343953926634992332820282019728792003956564819949",
        )
        .unwrap()
    }

    fn scalar_field_in_limbs() -> Vec<BLSScalar> {
        [
            BLSScalar::from_str("17592186044397").unwrap(),
            BLSScalar::from_str("17592186044415").unwrap(),
            BLSScalar::from_str("17592186044415").unwrap(),
            BLSScalar::from_str("17592186044415").unwrap(),
            BLSScalar::from_str("17592186044415").unwrap(),
            BLSScalar::from_str("34359738367").unwrap(),
        ]
        .to_vec()
    }

    fn scalar_field_sub_pad_in_limbs() -> Vec<BLSScalar> {
        [
            BLSScalar::from_str("35184372088794").unwrap(),
            BLSScalar::from_str("35184372088830").unwrap(),
            BLSScalar::from_str("35184372088830").unwrap(),
            BLSScalar::from_str("35184372088830").unwrap(),
            BLSScalar::from_str("35184372088830").unwrap(),
            BLSScalar::from_str("68719476734").unwrap(),
        ]
        .to_vec()
    }

    fn scalar_field_sub_pad_in_biguint() -> BigUint {
        BigUint::from_str(
            "115792089237316195423570985008687907853269984665640564039457584007913129639898",
        )
        .unwrap()
    }
}

#[cfg(test)]
mod test_ristretto {
    use crate::field_simulation::{SimFr, SimFrParams, SimFrParamsBLSRistretto};
    use algebra::bls12_381::BLSScalar;
    use algebra::prelude::*;
    use num_bigint::{BigUint, RandBigInt};
    use num_integer::Integer;

    type SimFrTest = SimFr<BLSScalar, SimFrParamsBLSRistretto>;

    #[test]
    fn test_sim_fr_biguint_conversion() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSRistretto::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
            let a_sim_fr = SimFrTest::from(&a);
            let a_recovered: BigUint = (&a_sim_fr).into();

            assert_eq!(a, a_recovered);
        }
    }

    #[test]
    fn test_sub() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSRistretto::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);

            let a_sim_fr = SimFrTest::from(&a);
            let b_sim_fr = SimFrTest::from(&b);
            let sum_sim_fr = &a_sim_fr - &b_sim_fr;

            let (_, sum) = a.add(&r_biguint).sub(&b).div_rem(&r_biguint);
            let (_, sum_recovered) =
                <&SimFrTest as Into<BigUint>>::into(&sum_sim_fr).div_rem(&r_biguint);

            assert_eq!(sum, sum_recovered);
        }
    }

    #[test]
    fn test_mul() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSRistretto::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);

            let a_sim_fr = SimFrTest::from(&a);
            let b_sim_fr = SimFrTest::from(&b);

            let prod_sim_fr_mul = a_sim_fr.mul(&b_sim_fr);
            let prod_sim_fr_mul_recovered: BigUint = (&prod_sim_fr_mul).into();

            let prod = &a * &b;

            assert_eq!(prod, prod_sim_fr_mul_recovered);
        }
    }

    #[test]
    fn test_enforce_zero_trivial() {
        let zero_fr = SimFrTest::from(&BigUint::zero());
        let zero_fr_mul = (&zero_fr) * (&zero_fr);

        zero_fr_mul.enforce_zero();
    }

    #[test]
    fn test_enforce_zero() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSRistretto::scalar_field_in_biguint();

        for _ in 0..1000 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);

            let a_fr = SimFrTest::from(&a);
            let b_fr = SimFrTest::from(&b);

            let ab_fr_mul = &a_fr * &b_fr;
            let ab_fr = &a * &b;
            assert_eq!(ab_fr, (&ab_fr_mul).into());

            let ab_fr_reduced = &ab_fr % &r_biguint;
            let ab_reduced = SimFrTest::from(&ab_fr_reduced);

            let zero_supposed = &ab_fr_mul - &ab_reduced;
            let zero_supposed_biguint: BigUint = (&zero_supposed).into();
            assert_eq!(BigUint::zero(), &zero_supposed_biguint % &r_biguint);
            zero_supposed.enforce_zero();
        }
    }

    #[test]
    #[should_panic]
    fn test_enforce_zero_panic() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSRistretto::scalar_field_in_biguint();

        let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
        let b = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);

        let a_fr = SimFrTest::from(&a);
        let b_fr = SimFrTest::from(&b);

        let ab_fr_mul = &a_fr * &b_fr;
        let ab_fr = &a * &b;
        assert_eq!(ab_fr, (&ab_fr_mul).into());

        let ab_fr_reduced_manipulated = &ab_fr % &r_biguint + &BigUint::from(10u64);
        let ab_reduced_manipulated = SimFrTest::from(&ab_fr_reduced_manipulated);

        let zero_supposed_manipulated = &ab_fr_mul - &ab_reduced_manipulated;
        zero_supposed_manipulated.enforce_zero();
    }
}

#[cfg(test)]
mod test_secq256k1 {
    use crate::field_simulation::{SimFr, SimFrParams, SimFrParamsBLSSecq256k1};
    use algebra::bls12_381::BLSScalar;
    use algebra::prelude::*;
    use num_bigint::{BigUint, RandBigInt};
    use num_integer::Integer;

    type SimFrTest = SimFr<BLSScalar, SimFrParamsBLSSecq256k1>;

    #[test]
    fn test_sim_fr_biguint_conversion() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSSecq256k1::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
            let a_sim_fr = SimFrTest::from(&a);
            let a_recovered: BigUint = (&a_sim_fr).into();

            assert_eq!(a, a_recovered);
        }
    }

    #[test]
    fn test_sub() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSSecq256k1::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);

            let a_sim_fr = SimFrTest::from(&a);
            let b_sim_fr = SimFrTest::from(&b);
            let sum_sim_fr = &a_sim_fr - &b_sim_fr;

            let (_, sum) = a.add(&r_biguint).sub(&b).div_rem(&r_biguint);
            let (_, sum_recovered) =
                <&SimFrTest as Into<BigUint>>::into(&sum_sim_fr).div_rem(&r_biguint);

            assert_eq!(sum, sum_recovered);
        }
    }

    #[test]
    fn test_mul() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSSecq256k1::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);

            let a_sim_fr = SimFrTest::from(&a);
            let b_sim_fr = SimFrTest::from(&b);

            let prod_sim_fr_mul = a_sim_fr.mul(&b_sim_fr);
            let prod_sim_fr_mul_recovered: BigUint = (&prod_sim_fr_mul).into();

            let prod = &a * &b;

            assert_eq!(prod, prod_sim_fr_mul_recovered);
        }
    }

    #[test]
    fn test_enforce_zero_trivial() {
        let zero_fr = SimFrTest::from(&BigUint::zero());
        let zero_fr_mul = (&zero_fr) * (&zero_fr);

        zero_fr_mul.enforce_zero();
    }

    #[test]
    fn test_enforce_zero() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSSecq256k1::scalar_field_in_biguint();

        for _ in 0..1000 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);

            let a_fr = SimFrTest::from(&a);
            let b_fr = SimFrTest::from(&b);

            let ab_fr_mul = &a_fr * &b_fr;
            let ab_fr = &a * &b;
            assert_eq!(ab_fr, (&ab_fr_mul).into());

            let ab_fr_reduced = &ab_fr % &r_biguint;
            let ab_reduced = SimFrTest::from(&ab_fr_reduced);

            let zero_supposed = &ab_fr_mul - &ab_reduced;
            let zero_supposed_biguint: BigUint = (&zero_supposed).into();
            assert_eq!(BigUint::zero(), &zero_supposed_biguint % &r_biguint);
            zero_supposed.enforce_zero();
        }
    }

    #[test]
    #[should_panic]
    fn test_enforce_zero_panic() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSSecq256k1::scalar_field_in_biguint();

        let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
        let b = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);

        let a_fr = SimFrTest::from(&a);
        let b_fr = SimFrTest::from(&b);

        let ab_fr_mul = &a_fr * &b_fr;
        let ab_fr = &a * &b;
        assert_eq!(ab_fr, (&ab_fr_mul).into());

        let ab_fr_reduced_manipulated = &ab_fr % &r_biguint + &BigUint::from(10u64);
        let ab_reduced_manipulated = SimFrTest::from(&ab_fr_reduced_manipulated);

        let zero_supposed_manipulated = &ab_fr_mul - &ab_reduced_manipulated;
        zero_supposed_manipulated.enforce_zero();
    }
}

#[cfg(test)]
mod test_zorro {
    use crate::field_simulation::{SimFr, SimFrParams, SimFrParamsBLSZorro};
    use algebra::bls12_381::BLSScalar;
    use algebra::prelude::*;
    use num_bigint::{BigUint, RandBigInt};
    use num_integer::Integer;

    type SimFrTest = SimFr<BLSScalar, SimFrParamsBLSZorro>;

    #[test]
    fn test_sim_fr_biguint_conversion() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSZorro::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
            let a_sim_fr = SimFrTest::from(&a);
            let a_recovered: BigUint = (&a_sim_fr).into();

            assert_eq!(a, a_recovered);
        }
    }

    #[test]
    fn test_sub() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSZorro::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);

            let a_sim_fr = SimFrTest::from(&a);
            let b_sim_fr = SimFrTest::from(&b);
            let sum_sim_fr = &a_sim_fr - &b_sim_fr;

            let (_, sum) = a.add(&r_biguint).sub(&b).div_rem(&r_biguint);
            let (_, sum_recovered) =
                <&SimFrTest as Into<BigUint>>::into(&sum_sim_fr).div_rem(&r_biguint);

            assert_eq!(sum, sum_recovered);
        }
    }

    #[test]
    fn test_mul() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSZorro::scalar_field_in_biguint();

        for _ in 0..100 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);

            let a_sim_fr = SimFrTest::from(&a);
            let b_sim_fr = SimFrTest::from(&b);

            let prod_sim_fr_mul = a_sim_fr.mul(&b_sim_fr);
            let prod_sim_fr_mul_recovered: BigUint = (&prod_sim_fr_mul).into();

            let prod = &a * &b;

            assert_eq!(prod, prod_sim_fr_mul_recovered);
        }
    }

    #[test]
    fn test_enforce_zero_trivial() {
        let zero_fr = SimFrTest::from(&BigUint::zero());
        let zero_fr_mul = (&zero_fr) * (&zero_fr);

        zero_fr_mul.enforce_zero();
    }

    #[test]
    fn test_enforce_zero() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSZorro::scalar_field_in_biguint();

        for _ in 0..1000 {
            let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
            let b = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);

            let a_fr = SimFrTest::from(&a);
            let b_fr = SimFrTest::from(&b);

            let ab_fr_mul = &a_fr * &b_fr;
            let ab_fr = &a * &b;
            assert_eq!(ab_fr, (&ab_fr_mul).into());

            let ab_fr_reduced = &ab_fr % &r_biguint;
            let ab_reduced = SimFrTest::from(&ab_fr_reduced);

            let zero_supposed = &ab_fr_mul - &ab_reduced;
            let zero_supposed_biguint: BigUint = (&zero_supposed).into();
            assert_eq!(BigUint::zero(), &zero_supposed_biguint % &r_biguint);
            zero_supposed.enforce_zero();
        }
    }

    #[test]
    #[should_panic]
    fn test_enforce_zero_panic() {
        let mut prng = test_rng();
        let r_biguint = SimFrParamsBLSZorro::scalar_field_in_biguint();

        let a = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);
        let b = prng.gen_biguint_range(&BigUint::zero(), &r_biguint);

        let a_fr = SimFrTest::from(&a);
        let b_fr = SimFrTest::from(&b);

        let ab_fr_mul = &a_fr * &b_fr;
        let ab_fr = &a * &b;
        assert_eq!(ab_fr, (&ab_fr_mul).into());

        let ab_fr_reduced_manipulated = &ab_fr % &r_biguint + &BigUint::from(10u64);
        let ab_reduced_manipulated = SimFrTest::from(&ab_fr_reduced_manipulated);

        let zero_supposed_manipulated = &ab_fr_mul - &ab_reduced_manipulated;
        zero_supposed_manipulated.enforce_zero();
    }
}
