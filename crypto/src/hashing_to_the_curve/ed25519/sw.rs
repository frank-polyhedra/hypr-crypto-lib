use crate::errors::Result;
use crate::hashing_to_the_curve::ed25519::elligator::Ed25519ElligatorParameters;
use crate::hashing_to_the_curve::models::elligator::ElligatorParameters;
use crate::hashing_to_the_curve::models::sw::SWParameters;
use algebra::ed25519::Ed25519Point;
use algebra::{ed25519::Ed25519Fq, new_ed25519_fq};

/// The SW map for ed25519.
pub struct Ed25519SWParameters;

impl SWParameters<Ed25519Point> for Ed25519SWParameters {
    const Z0: Ed25519Fq = new_ed25519_fq!(
        "7351004470711496783299639200077825248508346112056564349554070979984169706335"
    );
    const C1: Ed25519Fq = new_ed25519_fq!(
        "7351004470711496783299639200077825248508346112056564349554070979984169463003"
    );
    const C2: Ed25519Fq = new_ed25519_fq!(
        "14702008941422993566599278400155650497016692224113128699108141959968339412670"
    );
    const C3: Ed25519Fq = new_ed25519_fq!("1946658");
    const C4: Ed25519Fq = new_ed25519_fq!("-486664");
    const C5: Ed25519Fq = new_ed25519_fq!("2");
    const C6: Ed25519Fq = new_ed25519_fq!(
        "22595885493139578480537169384951274962349491958774703396425382945106958635058"
    );
    const A: Ed25519Fq = new_ed25519_fq!("486662");
    const B: Ed25519Fq = new_ed25519_fq!("1");
    const C: Ed25519Fq = new_ed25519_fq!("0");
    const QNR: Ed25519Fq = new_ed25519_fq!("2");

    fn convert_to_group(x: &Ed25519Fq, y: &Ed25519Fq) -> Result<Ed25519Point> {
        Ed25519ElligatorParameters::convert_to_group(x, y)
    }

    fn convert_from_group(p: &Ed25519Point) -> Result<(Ed25519Fq, Ed25519Fq)> {
        Ed25519ElligatorParameters::convert_from_group(p)
    }
}

#[cfg(test)]
mod tests {
    use crate::hashing_to_the_curve::ed25519::sw::Ed25519SWParameters;
    use crate::hashing_to_the_curve::models::sw::SWMap;
    use crate::hashing_to_the_curve::traits::HashingToCurve;
    use algebra::ed25519::{Ed25519Fq, Ed25519Point};
    use algebra::new_ed25519_fq;
    use algebra::prelude::*;

    type M = SWMap<Ed25519Point, Ed25519SWParameters>;

    #[test]
    fn test_x_derivation() {
        let mut t: Ed25519Fq = new_ed25519_fq!("7836");

        let x1 = M::x1(&t).unwrap();
        let x2 = M::x2(&t, &x1).unwrap();
        let x3 = M::x3(&t).unwrap();

        assert_eq!(
            x1,
            new_ed25519_fq!(
                "35052544075417610700660092540301712605483067939443826766625142601993311385282"
            )
        );
        assert_eq!(
            x2,
            new_ed25519_fq!(
                "22843500543240487011125399964042241321151924393376455253103649401963252948003"
            )
        );
        assert_eq!(
            x3,
            new_ed25519_fq!(
                "55628280783676121122135371125950213811806717931300590918014233701929027895981"
            )
        );

        t = new_ed25519_fq!(
            "26261490946361586592261280563100114235157954222781295781974865328952772526824"
        );

        let x1 = M::x1(&t).unwrap();
        let x2 = M::x2(&t, &x1).unwrap();
        let x3 = M::x3(&t).unwrap();

        assert_eq!(
            x1,
            new_ed25519_fq!(
                "55662970774143248676152068296021054624113686786963469155330127785619018187083"
            )
        );
        assert_eq!(
            x2,
            new_ed25519_fq!(
                "2233073844514849035633424208322899302521305545856812864398664218337546146202"
            )
        );
        assert_eq!(
            x3,
            new_ed25519_fq!(
                "53840827294954389625880150540438237547370106120164461777668468238174198448700"
            )
        );
    }

    #[test]
    fn test_random_t() {
        for _ in 0..100 {
            let mut rng = test_rng();
            let t = Ed25519Fq::random(&mut rng);

            let final_x = M::get_cofactor_uncleared_x(&t).unwrap();
            let (final_x2, trace) = M::get_cofactor_uncleared_x_and_trace(&t).unwrap();

            assert_eq!(final_x, final_x2);
            assert!(M::verify_trace(&t, &final_x, &trace));
            assert!(M::is_x_on_curve(&final_x));
        }
    }

    #[test]
    fn test_group_conversion() {
        for _ in 0..100 {
            let mut rng = test_rng();
            let p = Ed25519Point::random(&mut rng);

            let p_conv = M::convert_from_group(&p).unwrap();
            let p_rec = M::convert_to_group(&p_conv.0, &p_conv.1).unwrap();
            assert_eq!(p, p_rec);
        }
    }
}
