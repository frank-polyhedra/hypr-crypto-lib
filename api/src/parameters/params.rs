use crate::anon_xfr::abar_to_abar::{build_multi_xfr_cs, AXfrWitness};
use crate::anon_xfr::ar_to_abar::build_ar_to_abar_cs;
use crate::anon_xfr::ownership::build_ownership_cs;
use crate::anon_xfr::{commit, nullify, AXfrAddressFoldingWitness, TurboPlonkCS, TREE_DEPTH};
use crate::errors::{Error, Result};
use crate::keys::KeyPair;
use crate::parameters::{
    AddressFormat::{ED25519, SECP256K1},
    ABAR_TO_ABAR_VERIFIER_COMMON_PARAMS, ABAR_TO_ABAR_VERIFIER_ED25519_SPECIFIC_PARAMS,
    ABAR_TO_ABAR_VERIFIER_SECP256K1_SPECIFIC_PARAMS, AR_TO_ABAR_VERIFIER_PARAMS, LAGRANGE_BASES,
    OWNERSHIP_ED25519_VERIFIER_PARAMS, OWNERSHIP_SECP256K1_VERIFIER_PARAMS, SRS,
};
use crate::structs::{MTNode, MTPath, PayeeWitness, PayerWitness};
use algebra::bn254::{BN254Scalar, BN254G1};
use algebra::prelude::*;
use ark_std::{collections::BTreeMap, format};
use num_traits::Zero;
use plonk::plonk::constraint_system::ConstraintSystem;
use plonk::plonk::indexer::{indexer_with_lagrange, PlonkPK, PlonkVK};
use plonk::poly_commit::kzg_poly_com::KZGCommitmentSchemeBN254;
use plonk::poly_commit::pcs::PolyComScheme;
use rand_chacha::ChaChaRng;
use rand_core::SeedableRng;

/// The range in the Bulletproofs range check.
pub const BULLET_PROOF_RANGE: usize = 32;
/// The maximal number
pub const MAX_CONFIDENTIAL_RECORD_NUMBER: usize = 128;
/// The maximal number of inputs and outputs supported by this setup program, for standard payments.
pub const MAX_ANONYMOUS_RECORD_NUMBER_STANDARD: usize = 5;
/// The maximal number of outputs supported by this setup program, for airport.
pub const MAX_ANONYMOUS_RECORD_NUMBER_ONE_INPUT: usize = 18;
/// The default number of Bulletproofs generators
pub const DEFAULT_BP_NUM_GENS: usize = 256;
/// The number of the Bulletproofs(over the Secq256k1 curve) generators needed for anonymous transfer.
pub const ANON_XFR_BP_GENS_LEN: usize = 2048;

#[derive(Serialize, Deserialize)]
/// The verifier parameters.
pub struct VerifierParams {
    /// A label that describes the prover parameters.
    pub label: String,
    /// The shrunk version of the polynomial commitment scheme.
    pub shrunk_vk: KZGCommitmentSchemeBN254,
    /// The shrunk version of the constraint system.
    pub shrunk_cs: TurboPlonkCS,
    /// The TurboPlonk verifying key.
    pub verifier_params: PlonkVK<KZGCommitmentSchemeBN254>,
}

#[derive(Serialize, Deserialize)]
/// The common part of the verifier parameters.
pub struct VerifierParamsSplitCommon {
    /// The shrunk version of the polynomial commitment scheme.
    pub shrunk_pcs: KZGCommitmentSchemeBN254,
}

#[derive(Serialize, Deserialize)]
/// The specific part of the verifier parameters.
pub struct VerifierParamsSplitSpecific {
    /// A label that describes the prover parameters.
    pub label: String,
    /// The shrunk version of the constraint system.
    pub shrunk_cs: TurboPlonkCS,
    /// The verifier parameters.
    pub verifier_params: PlonkVK<KZGCommitmentSchemeBN254>,
}

/// The address format.
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum AddressFormat {
    /// Secp256k1 address
    SECP256K1,
    /// Ed25519 address
    ED25519,
}

impl ProverParams {
    /// Obtain the parameters for anonymous transfer for a given number of inputs and a given number of outputs.
    pub fn gen_abar_to_abar(
        n_payers: usize,
        n_payees: usize,
        address_format: AddressFormat,
    ) -> Result<ProverParams> {
        let label = match address_format {
            SECP256K1 => format!("abar_to_abar_{}_to_{}_secp256k1", n_payees, n_payers),
            ED25519 => format!("abar_to_abar_{}_to_{}_ed25519", n_payees, n_payers),
        };

        let fake_witness = AXfrWitness::fake(n_payers, n_payees, 0, address_format);

        let mut nullifiers_traces = Vec::new();
        let mut input_commitments_traces = Vec::new();
        let mut output_commitments_traces = Vec::new();
        for payer_witness in fake_witness.payers_witnesses.iter() {
            let (_, trace) = nullify(
                &payer_witness.secret_key.clone().into_keypair(),
                payer_witness.amount,
                payer_witness.asset_type,
                payer_witness.uid,
            )?;
            nullifiers_traces.push(trace);

            let (_, trace) = commit(
                &payer_witness.secret_key.clone().into_keypair().get_pk(),
                payer_witness.blind,
                payer_witness.amount,
                payer_witness.asset_type,
            )?;
            input_commitments_traces.push(trace);
        }

        for payee_witness in fake_witness.payees_witnesses.iter() {
            let (_, trace) = commit(
                &payee_witness.public_key,
                payee_witness.blind,
                payee_witness.amount,
                payee_witness.asset_type,
            )?;
            output_commitments_traces.push(trace);
        }

        let (cs, _) = build_multi_xfr_cs(
            &fake_witness,
            &nullifiers_traces,
            &input_commitments_traces,
            &output_commitments_traces,
            &AXfrAddressFoldingWitness::default(address_format),
        );
        let cs_size = cs.size();
        let pcs = load_srs_params(cs_size)?;
        let lagrange_pcs = load_lagrange_params(cs_size);

        let verifier_params =
            if let Ok(v) = VerifierParams::load_abar_to_abar(n_payers, n_payees, address_format) {
                Some(v.verifier_params)
            } else {
                None
            };

        let prover_params =
            indexer_with_lagrange(&cs, &pcs, lagrange_pcs.as_ref(), verifier_params).unwrap();

        Ok(ProverParams {
            label,
            pcs,
            lagrange_pcs,
            cs,
            prover_params,
        })
    }

    /// Obtain the parameters for transparent to anonymous.
    pub fn gen_ar_to_abar() -> Result<ProverParams> {
        let label = String::from("ar_to_abar");

        let elem_zero = BN254Scalar::zero();

        // It's okay to choose a fixed seed to build CS.
        let mut prng = ChaChaRng::from_seed([0u8; 32]);

        // It's okay to choose a fixed address format.
        let keypair = KeyPair::sample(&mut prng, SECP256K1);

        let dummy_payee = PayeeWitness {
            amount: 0,
            blind: elem_zero,
            asset_type: elem_zero,
            public_key: keypair.get_pk(),
        };
        let (_, input_commitment_trace) = commit(
            &dummy_payee.public_key,
            dummy_payee.blind,
            dummy_payee.amount,
            dummy_payee.asset_type,
        )?;
        let (cs, _) = build_ar_to_abar_cs(dummy_payee, &input_commitment_trace);

        let cs_size = cs.size();
        let pcs = load_srs_params(cs_size)?;
        let lagrange_pcs = load_lagrange_params(cs_size);

        let verifier_params = match VerifierParams::load_ar_to_abar().ok() {
            Some(v) => Some(v.verifier_params),
            None => None,
        };

        let prover_params =
            indexer_with_lagrange(&cs, &pcs, lagrange_pcs.as_ref(), verifier_params).unwrap();

        Ok(ProverParams {
            label,
            pcs,
            lagrange_pcs,
            cs,
            prover_params,
        })
    }

    /// Obtain the parameters for anonymous to transparent with ownership.
    pub fn gen_ownership(address_format: AddressFormat) -> Result<ProverParams> {
        let label = match address_format {
            SECP256K1 => String::from("ownership_secp256k1"),
            ED25519 => String::from("ownership_ed25519"),
        };
        let verifier_params = match VerifierParams::load_ownership(address_format).ok() {
            Some(v) => Some(v.verifier_params),
            None => None,
        };

        let elem_zero = BN254Scalar::zero();

        // It's okay to choose a fixed seed to build CS.
        let mut prng = ChaChaRng::from_seed([0u8; 32]);

        let node = MTNode {
            left: elem_zero,
            mid: elem_zero,
            right: elem_zero,
            is_left_child: 0,
            is_mid_child: 0,
            is_right_child: 0,
        };

        let keypair = KeyPair::sample(&mut prng, address_format);
        let payer_secret = PayerWitness {
            secret_key: keypair.get_sk(),
            uid: 0,
            amount: 0,
            asset_type: elem_zero,
            path: MTPath::new(vec![node.clone(); TREE_DEPTH]),
            blind: elem_zero,
        };
        let (_, nullifier_trace) = nullify(
            &payer_secret.secret_key.clone().into_keypair(),
            payer_secret.amount,
            payer_secret.asset_type,
            payer_secret.uid,
        )?;

        let (_, input_commitment_trace) = commit(
            &payer_secret.secret_key.clone().into_keypair().get_pk(),
            payer_secret.blind,
            payer_secret.amount,
            payer_secret.asset_type,
        )?;

        let (cs, _) = build_ownership_cs(
            &payer_secret,
            &nullifier_trace,
            &input_commitment_trace,
            &AXfrAddressFoldingWitness::default(address_format),
        );

        let cs_size = cs.size();
        let pcs = load_srs_params(cs_size)?;
        let lagrange_pcs = load_lagrange_params(cs_size);

        let prover_params =
            indexer_with_lagrange(&cs, &pcs, lagrange_pcs.as_ref(), verifier_params).unwrap();

        Ok(ProverParams {
            label,
            pcs,
            lagrange_pcs,
            cs,
            prover_params,
        })
    }
}

impl VerifierParams {
    /// Load the verifier parameters for a given number of inputs and a given number of outputs.
    pub fn get_abar_to_abar(
        n_payers: usize,
        n_payees: usize,
        address_format: AddressFormat,
    ) -> Result<VerifierParams> {
        if !(n_payees <= MAX_ANONYMOUS_RECORD_NUMBER_STANDARD
            && n_payers <= MAX_ANONYMOUS_RECORD_NUMBER_STANDARD
            || n_payers == 1 && n_payees <= MAX_ANONYMOUS_RECORD_NUMBER_ONE_INPUT)
        {
            Err(Error::MissingVerifierParamsError)
        } else {
            match Self::load_abar_to_abar(n_payers, n_payees, address_format) {
                Ok(vk) => Ok(vk),
                Err(_e) => Ok(Self::from(ProverParams::gen_abar_to_abar(
                    n_payers,
                    n_payees,
                    address_format,
                )?)),
            }
        }
    }

    /// Load the verifier parameters from prepare.
    pub fn load_abar_to_abar(
        n_payers: usize,
        n_payees: usize,
        address_format: AddressFormat,
    ) -> Result<VerifierParams> {
        let verifier_specific_params = match address_format {
            SECP256K1 => ABAR_TO_ABAR_VERIFIER_SECP256K1_SPECIFIC_PARAMS,
            ED25519 => ABAR_TO_ABAR_VERIFIER_ED25519_SPECIFIC_PARAMS,
        };

        let label = match address_format {
            SECP256K1 => format!("abar_to_abar_{}_to_{}_secp256k1", n_payees, n_payers),
            ED25519 => format!("abar_to_abar_{}_to_{}_ed25519", n_payees, n_payers),
        };

        match (
            ABAR_TO_ABAR_VERIFIER_COMMON_PARAMS,
            verifier_specific_params,
        ) {
            (Some(c_bytes), Some(s_bytes)) => {
                let common: VerifierParamsSplitCommon =
                    bincode::deserialize(c_bytes).map_err(|_| Error::DeserializationError)?;
                let specials: BTreeMap<(usize, usize), Vec<u8>> =
                    bincode::deserialize(s_bytes).unwrap();
                let special_bytes = specials.get(&(n_payers, n_payees));
                if special_bytes.is_none() {
                    return Err(Error::DeserializationError);
                }
                let special: VerifierParamsSplitSpecific =
                    bincode::deserialize(special_bytes.unwrap())
                        .map_err(|_| Error::DeserializationError)?;

                if special.label != label {
                    return Err(Error::AXfrVerifierParamsError);
                }

                Ok(VerifierParams {
                    label,
                    shrunk_vk: common.shrunk_pcs,
                    shrunk_cs: special.shrunk_cs,
                    verifier_params: special.verifier_params,
                })
            }
            _ => Err(Error::MissingVerifierParamsError),
        }
    }

    /// Obtain the parameters for transparent to anonymous.
    pub fn get_ar_to_abar() -> Result<VerifierParams> {
        match Self::load_ar_to_abar() {
            Ok(vk) => Ok(vk),
            _ => {
                let prover_params = ProverParams::gen_ar_to_abar()?;
                Ok(VerifierParams::from(prover_params))
            }
        }
    }

    /// Obtain the parameters for transparent to anonymous from prepare.
    pub fn load_ar_to_abar() -> Result<VerifierParams> {
        if let Some(bytes) = AR_TO_ABAR_VERIFIER_PARAMS {
            let verifier_params = bincode::deserialize::<VerifierParams>(bytes);
            if let Ok(verifier_params) = verifier_params {
                if verifier_params.label != *"ar_to_abar" {
                    Err(Error::MissingVerifierParamsError)
                } else {
                    Ok(verifier_params)
                }
            } else {
                Err(Error::DeserializationError)
            }
        } else {
            Err(Error::MissingVerifierParamsError)
        }
    }

    /// Obtain the parameters for anonymous to transparent with ownership.
    pub fn get_ownership(address_format: AddressFormat) -> Result<VerifierParams> {
        match Self::load_ownership(address_format) {
            Ok(vk) => Ok(vk),
            _ => {
                let prover_params = ProverParams::gen_ownership(address_format)?;
                Ok(VerifierParams::from(prover_params))
            }
        }
    }

    /// Obtain the parameters for anonymous to transparent with ownership from prepare.
    pub fn load_ownership(address_format: AddressFormat) -> Result<VerifierParams> {
        let bytes = match address_format {
            SECP256K1 => OWNERSHIP_SECP256K1_VERIFIER_PARAMS,
            ED25519 => OWNERSHIP_ED25519_VERIFIER_PARAMS,
        };

        if let Some(bytes) = bytes {
            let verifier_params = bincode::deserialize::<VerifierParams>(bytes);
            if let Ok(verifier_params) = verifier_params {
                let label = match address_format {
                    SECP256K1 => String::from("ownership_secp256k1"),
                    ED25519 => String::from("ownership_ed25519"),
                };

                if verifier_params.label != label {
                    Err(Error::MissingVerifierParamsError)
                } else {
                    Ok(verifier_params)
                }
            } else {
                Err(Error::DeserializationError)
            }
        } else {
            Err(Error::MissingVerifierParamsError)
        }
    }

    /// Split the verifier parameters to the common part and the sspecific part.
    pub fn split(self) -> Result<(VerifierParamsSplitCommon, VerifierParamsSplitSpecific)> {
        Ok((
            VerifierParamsSplitCommon {
                shrunk_pcs: self.shrunk_vk.shrink_to_verifier_only(),
            },
            VerifierParamsSplitSpecific {
                label: self.label,
                shrunk_cs: self.shrunk_cs.shrink_to_verifier_only(),
                verifier_params: self.verifier_params,
            },
        ))
    }
}

impl From<ProverParams> for VerifierParams {
    fn from(params: ProverParams) -> Self {
        VerifierParams {
            label: params.label,
            shrunk_vk: params.pcs.shrink_to_verifier_only(),
            shrunk_cs: params.cs.shrink_to_verifier_only(),
            verifier_params: params.prover_params.get_verifier_params(),
        }
    }
}

#[derive(Serialize, Deserialize)]
/// The prover parameters.
pub struct ProverParams {
    /// A label that describes the prover parameters.
    pub label: String,
    /// The full SRS for the polynomial commitment scheme.
    pub pcs: KZGCommitmentSchemeBN254,
    /// The Lagrange basis format of SRS.
    pub lagrange_pcs: Option<KZGCommitmentSchemeBN254>,
    /// The constraint system.
    pub cs: TurboPlonkCS,
    /// The TurboPlonk proving key.
    pub prover_params: PlonkPK<KZGCommitmentSchemeBN254>,
}

fn load_lagrange_params(size: usize) -> Option<KZGCommitmentSchemeBN254> {
    match LAGRANGE_BASES.get(&size) {
        None => None,
        Some(bytes) => KZGCommitmentSchemeBN254::from_unchecked_bytes(bytes).ok(),
    }
}

fn load_srs_params(size: usize) -> Result<KZGCommitmentSchemeBN254> {
    let srs = SRS.ok_or(Error::MissingSRSError)?;

    let KZGCommitmentSchemeBN254 {
        public_parameter_group_1,
        public_parameter_group_2,
    } = KZGCommitmentSchemeBN254::from_unchecked_bytes(srs)?;

    let mut new_group_1 = vec![BN254G1::default(); core::cmp::max(size + 3, 2051)];
    new_group_1[0..2051].copy_from_slice(&public_parameter_group_1[0..2051]);

    if size == 4096 {
        new_group_1[4096..4099].copy_from_slice(&public_parameter_group_1[2051..2054]);
    }

    if size == 8192 {
        new_group_1[8192..8195].copy_from_slice(&public_parameter_group_1[2054..2057]);
    }

    if size > 8192 {
        return Err(Error::ParameterError);
    }

    Ok(KZGCommitmentSchemeBN254 {
        public_parameter_group_2,
        public_parameter_group_1: new_group_1,
    })
}

#[cfg(test)]
mod test {
    use crate::parameters::params::load_srs_params;
    use crate::parameters::params::AddressFormat::{ED25519, SECP256K1};
    use crate::parameters::params::ProverParams;
    use crate::parameters::params::VerifierParams;
    use algebra::{
        bn254::{BN254Scalar, BN254G1},
        prelude::*,
    };
    use plonk::poly_commit::{field_polynomial::FpPolynomial, pcs::PolyComScheme};

    #[test]
    fn test_params_serialization() {
        let params = ProverParams::gen_abar_to_abar(1, 1, SECP256K1).unwrap();

        let v = bincode::serialize(&params).unwrap();
        let params_de: ProverParams = bincode::deserialize(&v).unwrap();
        let v2 = bincode::serialize(&params_de).unwrap();
        assert_eq!(v, v2);

        let params = ProverParams::gen_abar_to_abar(1, 1, ED25519).unwrap();

        let v = bincode::serialize(&params).unwrap();
        let params_de: ProverParams = bincode::deserialize(&v).unwrap();
        let v2 = bincode::serialize(&params_de).unwrap();
        assert_eq!(v, v2);
    }

    #[test]
    fn test_vk_params_serialization() {
        let params = VerifierParams::get_abar_to_abar(3, 3, SECP256K1).unwrap();
        let v = bincode::serialize(&params).unwrap();
        let params_de: VerifierParams = bincode::deserialize(&v).unwrap();
        let v2 = bincode::serialize(&params_de).unwrap();
        assert_eq!(v, v2);

        let params = VerifierParams::get_abar_to_abar(3, 3, ED25519).unwrap();
        let v = bincode::serialize(&params).unwrap();
        let params_de: VerifierParams = bincode::deserialize(&v).unwrap();
        let v2 = bincode::serialize(&params_de).unwrap();
        assert_eq!(v, v2);
    }

    #[test]
    fn test_crs_commit() {
        let pcs = load_srs_params(16).unwrap();

        let one = BN254Scalar::one();
        let two = one.add(&one);
        let three = two.add(&one);
        let six = three.add(&three);

        let fq_poly = FpPolynomial::from_coefs(vec![two, three, six]);
        let commitment = pcs.commit(&fq_poly).unwrap();

        let coefs_poly_blsscalar = fq_poly.get_coefs_ref().iter().collect_vec();
        let mut expected_committed_value = BN254G1::get_identity();

        // Doing the multiexp by hand
        for (i, coef) in coefs_poly_blsscalar.iter().enumerate() {
            let g_i = pcs.public_parameter_group_1[i].clone();
            expected_committed_value = expected_committed_value.add(&g_i.mul(&coef));
        }
        assert_eq!(expected_committed_value, commitment.0);
    }
}
