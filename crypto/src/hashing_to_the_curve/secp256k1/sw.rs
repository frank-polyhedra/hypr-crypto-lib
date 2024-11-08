use crate::errors::Result;
use crate::hashing_to_the_curve::models::sw::SWParameters;
use algebra::prelude::*;
use algebra::secp256k1::SECP256K1G1;
use algebra::{new_secp256k1_fq, secp256k1::SECP256K1Fq};

/// The SW map for secp256k1.
pub struct Secp256k1SWParameters;

impl SWParameters<SECP256K1G1> for Secp256k1SWParameters {
    const Z0: SECP256K1Fq = new_secp256k1_fq!(
        "2301468970328204842700089520541121182249040118132057797950280022211810753577"
    );
    const C1: SECP256K1Fq = new_secp256k1_fq!(
        "60197513588986302554485582024885075108884032450952339817679072026166228089409"
    );
    const C2: SECP256K1Fq = new_secp256k1_fq!(
        "4602937940656409685400179041082242364498080236264115595900560044423621507154"
    );
    const C3: SECP256K1Fq = new_secp256k1_fq!("6");
    const C4: SECP256K1Fq = new_secp256k1_fq!("1");
    const C5: SECP256K1Fq = new_secp256k1_fq!(
        "115792089237316195423570985008687907853269984665640564039457584007908834671662"
    );
    const C6: SECP256K1Fq = new_secp256k1_fq!(
        "38597363079105398474523661669562635951089994888546854679819194669302944890554"
    );
    const A: SECP256K1Fq = new_secp256k1_fq!("0");
    const B: SECP256K1Fq = new_secp256k1_fq!("0");
    const C: SECP256K1Fq = new_secp256k1_fq!("7");
    const QNR: SECP256K1Fq = new_secp256k1_fq!("-1");

    fn convert_to_group(x: &SECP256K1Fq, y: &SECP256K1Fq) -> Result<SECP256K1G1> {
        Ok(SECP256K1G1::new(x, y))
    }

    fn convert_from_group(p: &SECP256K1G1) -> Result<(SECP256K1Fq, SECP256K1Fq)> {
        Ok((p.get_x(), p.get_y()))
    }
}

#[cfg(test)]
mod tests {
    use crate::hashing_to_the_curve::models::sw::SWMap;
    use crate::hashing_to_the_curve::secp256k1::sw::Secp256k1SWParameters;
    use crate::hashing_to_the_curve::traits::HashingToCurve;
    use algebra::new_secp256k1_fq;
    use algebra::prelude::*;
    use algebra::secp256k1::{SECP256K1Fq, SECP256K1G1};

    type M = SWMap<SECP256K1G1, Secp256k1SWParameters>;

    #[test]
    fn test_x_derivation() {
        let mut t: SECP256K1Fq = new_secp256k1_fq!("7836");

        let x1 = M::x1(&t).unwrap();
        let x2 = M::x2(&t, &x1).unwrap();
        let x3 = M::x3(&t).unwrap();

        assert_eq!(
            x1,
            new_secp256k1_fq!(
                "12173361532131623274578764961252033537537011288282760545929785782471408876466"
            )
        );
        assert_eq!(
            x2,
            new_secp256k1_fq!(
                "103618727705184572148992220047435874315732973377357803493527798225437425795198"
            )
        );
        assert_eq!(
            x3,
            new_secp256k1_fq!(
                "74087608966983262623115840088572810691661208660740673962981321521047702830003"
            )
        );

        t = new_secp256k1_fq!(
            "26261490946361586592261280563100114235157954222781295781974865328952772526824"
        );

        let x1 = M::x1(&t).unwrap();
        let x2 = M::x2(&t, &x1).unwrap();
        let x3 = M::x3(&t).unwrap();

        assert_eq!(
            x1,
            new_secp256k1_fq!(
                "26139849459076662048090509060200323109571459447699535307492857403137446071407"
            )
        );
        assert_eq!(
            x2,
            new_secp256k1_fq!(
                "89652239778239533375480475948487584743698525217941028731964726604771388600257"
            )
        );
        assert_eq!(
            x3,
            new_secp256k1_fq!(
                "57498912498287391356729542970652380787836579419942546263322241630256315967730"
            )
        );
    }

    #[test]
    fn test_random_t() {
        for _ in 0..100 {
            let mut rng = test_rng();
            let t = SECP256K1Fq::random(&mut rng);

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
            let p = SECP256K1G1::random(&mut rng);

            let p_conv = M::convert_from_group(&p).unwrap();
            let p_rec = M::convert_to_group(&p_conv.0, &p_conv.1).unwrap();
            assert_eq!(p, p_rec);
        }
    }
}
