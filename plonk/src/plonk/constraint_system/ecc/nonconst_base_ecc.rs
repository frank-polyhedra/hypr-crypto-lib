use crate::plonk::constraint_system::ecc::{ExtendedPointVar, PointVar};
use crate::plonk::constraint_system::{TurboCS, VarIndex};
use algebra::prelude::*;
use algebra::traits::TECurve;

impl<S: Scalar> TurboCS<S> {
    /// Returns an identity twisted Edwards point and its corresponding point variable
    fn get_identity<T: TECurve<BaseType = S>>(&mut self) -> ExtendedPointVar<T> {
        ExtendedPointVar(PointVar(self.zero_var(), self.one_var()), T::get_identity())
    }

    /// Given two (extended) point variables `point0`, `point1`, and a Boolean variable `bit`,
    /// returns `point_bit`.
    fn select_nonconstant_points<T: TECurve<BaseType = S>>(
        &mut self,
        point0: &ExtendedPointVar<T>,
        point1: &ExtendedPointVar<T>,
        bit: VarIndex,
    ) -> ExtendedPointVar<T> {
        let point0_var = &point0.0;
        let point1_var = &point1.0;
        let x = self.select(point0_var.0, point1_var.0, bit);
        let y = self.select(point0_var.1, point1_var.1, bit);
        let res_point_var = PointVar(x, y);
        if self.witness[bit].is_zero() {
            ExtendedPointVar(res_point_var, point0.1)
        } else {
            ExtendedPointVar(res_point_var, point1.1)
        }
    }

    ///  Non-constant-base scalar multiplication:
    ///  Given a base point `[G]` and an `n_bits`-bit secret scalar `s`, returns `s * [G]`.
    /// `n_bits` should be a positive even number.
    pub fn nonconst_base_scalar_mul<T: TECurve<BaseType = S>>(
        &mut self,
        base_var: PointVar,
        base: T,
        scalar_var: VarIndex,
        n_bits: usize,
    ) -> PointVar {
        assert!(n_bits > 0, "n_bits is not positive");

        let b_scalar_var = self.range_check(scalar_var, n_bits);

        let mut res_ext = self.get_identity();
        let identity = self.get_identity();
        let extended_point = ExtendedPointVar(base_var, base);

        for &bit in b_scalar_var.iter().rev() {
            // doubling
            res_ext = self.ecc_add(&res_ext.0, &res_ext.0, &res_ext.1, &res_ext.1);
            // conditional addition
            let tmp_ext = self.select_nonconstant_points(&identity, &extended_point, bit);
            res_ext = self.ecc_add(&res_ext.0, &tmp_ext.0, &res_ext.1, &tmp_ext.1);
        }
        res_ext.0
    }
}

#[cfg(test)]
mod test {
    use crate::plonk::constraint_system::TurboCS;
    use algebra::{
        baby_jubjub::BabyJubjubPoint, ed25519::Ed25519Point, jubjub::JubjubPoint, prelude::*,
        traits::TECurve,
    };

    #[test]
    fn test_scalar_mul() {
        scalar_mul::<JubjubPoint>();
        scalar_mul::<BabyJubjubPoint>();
        scalar_mul::<Ed25519Point>();
    }

    fn scalar_mul<T: TECurve>() {
        let mut cs = TurboCS::new();

        // compute secret scalar
        let scalar_bytes = [
            17, 144, 47, 113, 34, 14, 11, 207, 13, 116, 200, 201, 17, 33, 101, 116, 0, 59, 51, 1,
            2, 39, 13, 56, 69, 175, 41, 111, 134, 180, 0, 0,
        ];
        let scalar = T::BaseType::from_bytes(&scalar_bytes).unwrap();
        let jubjub_scalar = T::ScalarType::from_bytes(&scalar_bytes).unwrap(); // safe unwrap
        let base_ext = T::get_base();
        let p_out_ext = base_ext.mul(&jubjub_scalar);
        let p_out_plus_ext = p_out_ext.add(&base_ext);

        // build circuit
        let base_var = cs.new_point_variable(base_ext);
        let scalar_var = cs.new_variable(scalar);
        let p_out_var = cs.nonconst_base_scalar_mul(base_var, base_ext, scalar_var, 256);
        let mut witness = cs.get_and_clear_witness();
        cs.verify_witness(&witness[..], &[]).unwrap();

        // wrong witness: point = GENERATOR * (scalar + 1)
        witness[p_out_var.0] = p_out_plus_ext.get_x();
        witness[p_out_var.1] = p_out_plus_ext.get_y();
        assert!(cs.verify_witness(&witness[..], &[]).is_err());
    }

    #[test]
    fn test_scalar_mul_with_zero_scalar() {
        scalar_mul_with_zero_scalar::<JubjubPoint>();
        scalar_mul_with_zero_scalar::<BabyJubjubPoint>();
        scalar_mul_with_zero_scalar::<Ed25519Point>();
    }

    fn scalar_mul_with_zero_scalar<T: TECurve>() {
        let mut cs = TurboCS::new();
        let base_ext = T::get_base();

        let base_var = cs.new_point_variable(base_ext);
        let scalar_var = cs.new_variable(T::BaseType::zero());
        let p_out_var = cs.nonconst_base_scalar_mul(base_var, base_ext, scalar_var, 64);
        let mut witness = cs.get_and_clear_witness();

        // check p_out is an identity point
        assert_eq!(witness[p_out_var.0], T::BaseType::zero());
        assert_eq!(witness[p_out_var.1], T::BaseType::one());
        cs.verify_witness(&witness[..], &[]).unwrap();

        // wrong witness: p_out = GENERATOR
        witness[p_out_var.0] = base_ext.get_x();
        witness[p_out_var.1] = base_ext.get_y();
        assert!(cs.verify_witness(&witness[..], &[]).is_err());
    }
}
