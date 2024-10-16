use crate::anon_xfr::address_folding_ed25519::{
    create_address_folding_ed25519, prepare_verifier_input_ed25519,
    prove_address_folding_in_cs_ed25519, verify_address_folding_ed25519,
};
use crate::anon_xfr::address_folding_secp256k1::{
    create_address_folding_secp256k1, prepare_verifier_input_secp256k1,
    prove_address_folding_in_cs_secp256k1, verify_address_folding_secp256k1,
};
use crate::anon_xfr::{
    abar_to_abar::add_payers_witnesses, commit, commit_in_cs, compute_merkle_root_variables,
    nullify, nullify_in_cs, AXfrAddressFoldingInstance, AXfrAddressFoldingWitness, AXfrPlonkPf,
    TurboPlonkCS,
};
use crate::errors::{Error, Result};
use crate::keys::{KeyPair, SecretKey};
use crate::parameters::params::ProverParams;
use crate::parameters::params::VerifierParams;
use crate::structs::{AccElemVars, AssetType, Nullifier, OpenAnonAssetRecord, PayerWitness};
use algebra::{bn254::BN254Scalar, prelude::*};
use crypto::anemoi_jive::{AnemoiJive, AnemoiJive254, AnemoiVLHTrace, ANEMOI_JIVE_BN254_SALTS};
use digest::{consts::U64, Digest};
use merlin::Transcript;
use plonk::plonk::{
    constraint_system::{TurboCS, VarIndex},
    prover::prover_with_lagrange,
    verifier::verifier,
};

/// The domain separator for anonymous-to-transparent, for the Plonk proof.
const OWNERSHIP_PLONK_PROOF_TRANSCRIPT: &[u8] = b"Ownership Plonk Proof";

/// The domain separator for anonymous-to-transparent, for address folding.
const OWNERSHIP_FOLDING_PROOF_TRANSCRIPT: &[u8] = b"Ownership Folding Proof";

/// The anonymous-to-transparent note.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct OwnershipNote {
    /// The body part of ABAR to AR.
    pub body: OwnershipBody,
    /// The Plonk proof (assuming non-malleability).
    pub proof: AXfrPlonkPf,
    /// The address folding instance.
    pub folding_instance: AXfrAddressFoldingInstance,
}

/// The anonymous-to-transparent note without proof.
#[derive(Clone, Debug)]
pub struct OwnershipPreNote {
    /// The body part of ABAR to AR.
    pub body: OwnershipBody,
    /// Witness.
    pub witness: PayerWitness,
    /// The trace of the input commitment.
    pub input_commitment_trace: AnemoiVLHTrace<BN254Scalar, 2, 14>,
    /// The trace of the nullifier.
    pub nullifier_trace: AnemoiVLHTrace<BN254Scalar, 2, 14>,
    /// Input key pair.
    pub input_keypair: KeyPair,
}

/// The anonymous-to-transparent body.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct OwnershipBody {
    /// input ABAR being spent.
    pub input: Nullifier,
    /// The asset amount
    pub asset: AssetType,
    /// The asset amount
    pub amount: u128,
    /// The Merkle root hash.
    pub merkle_root: BN254Scalar,
    /// The Merkle root version.
    pub merkle_root_version: u64,
}

/// Generate an anonymous-to-transparent pre-note.
pub fn init_ownership_note(
    oabar: &OpenAnonAssetRecord,
    abar_keypair: &KeyPair,
) -> Result<OwnershipPreNote> {
    if oabar.mt_leaf_info.is_none() || abar_keypair.get_pk() != oabar.pub_key {
        return Err(Error::ParameterError);
    }

    let mt_leaf_info = oabar.mt_leaf_info.as_ref().unwrap();
    let (this_nullifier, this_nullifier_trace) = nullify(
        &abar_keypair,
        oabar.amount,
        oabar.asset_type.as_scalar(),
        mt_leaf_info.uid,
    )?;

    let (_, this_commitment_trace) = commit(
        &abar_keypair.get_pk(),
        oabar.blind,
        oabar.amount,
        oabar.asset_type.as_scalar(),
    )
    .unwrap();

    let payers_secret = PayerWitness {
        secret_key: abar_keypair.get_sk(),
        uid: mt_leaf_info.uid,
        amount: oabar.amount,
        asset_type: oabar.asset_type.as_scalar(),
        path: mt_leaf_info.path.clone(),
        blind: oabar.blind,
    };

    let mt_info_temp = oabar.mt_leaf_info.as_ref().unwrap();

    let body = OwnershipBody {
        input: this_nullifier,
        asset: oabar.asset_type,
        amount: oabar.amount,
        merkle_root: mt_info_temp.root,
        merkle_root_version: mt_info_temp.root_version,
    };

    Ok(OwnershipPreNote {
        body,
        witness: payers_secret,
        input_commitment_trace: this_commitment_trace,
        nullifier_trace: this_nullifier_trace,
        input_keypair: abar_keypair.clone(),
    })
}

/// Finalize an anonymous-to-transparent note.
pub fn finish_ownership_note<R: CryptoRng + RngCore, D: Digest<OutputSize = U64> + Default>(
    prng: &mut R,
    params: &ProverParams,
    pre_note: OwnershipPreNote,
    hash: D,
) -> Result<OwnershipNote> {
    let OwnershipPreNote {
        body,
        witness,
        input_commitment_trace,
        nullifier_trace,
        input_keypair,
    } = pre_note;

    let mut transcript = Transcript::new(OWNERSHIP_FOLDING_PROOF_TRANSCRIPT);

    let (folding_instance, folding_witness) = match input_keypair.get_sk_ref() {
        SecretKey::Secp256k1(_) => {
            let (folding_instance, folding_witness) =
                create_address_folding_secp256k1(prng, hash, &mut transcript, &input_keypair)?;
            (
                AXfrAddressFoldingInstance::Secp256k1(folding_instance),
                AXfrAddressFoldingWitness::Secp256k1(folding_witness),
            )
        }
        SecretKey::Ed25519(_) => {
            let (folding_instance, folding_witness) =
                create_address_folding_ed25519(prng, hash, &mut transcript, &input_keypair)?;
            (
                AXfrAddressFoldingInstance::Ed25519(folding_instance),
                AXfrAddressFoldingWitness::Ed25519(folding_witness),
            )
        }
    };

    let proof = prove_ownership(
        prng,
        params,
        &witness,
        &nullifier_trace,
        &input_commitment_trace,
        &folding_witness,
    )?;

    Ok(OwnershipNote {
        body,
        proof,
        folding_instance,
    })
}

/// Verify the anonymous-to-transparent note.
pub fn verify_ownership_note<D: Digest<OutputSize = U64> + Default>(
    params: &VerifierParams,
    note: &OwnershipNote,
    merkle_root: &BN254Scalar,
    hash: D,
) -> Result<()> {
    let mut transcript = Transcript::new(OWNERSHIP_FOLDING_PROOF_TRANSCRIPT);

    let address_folding_public_input = match &note.folding_instance {
        AXfrAddressFoldingInstance::Secp256k1(a) => {
            let (beta, lambda) = verify_address_folding_secp256k1(hash, &mut transcript, a)?;
            prepare_verifier_input_secp256k1(&a, &beta, &lambda)
        }
        AXfrAddressFoldingInstance::Ed25519(a) => {
            let (beta, lambda) = verify_address_folding_ed25519(hash, &mut transcript, a)?;
            prepare_verifier_input_ed25519(&a, &beta, &lambda)
        }
    };

    if *merkle_root != note.body.merkle_root {
        return Err(Error::AXfrVerificationError);
    }

    let mut transcript = Transcript::new(OWNERSHIP_PLONK_PROOF_TRANSCRIPT);
    let mut online_inputs = vec![];
    online_inputs.push(note.body.input.clone());
    online_inputs.push(merkle_root.clone());
    online_inputs.push(BN254Scalar::from(note.body.amount));
    online_inputs.push(note.body.asset.as_scalar());
    online_inputs.extend_from_slice(&address_folding_public_input);

    Ok(verifier(
        &mut transcript,
        &params.shrunk_vk,
        &params.shrunk_cs,
        &params.verifier_params,
        &online_inputs,
        &note.proof,
    )?)
}

fn prove_ownership<R: CryptoRng + RngCore>(
    rng: &mut R,
    params: &ProverParams,
    payers_witness: &PayerWitness,
    nullifier_trace: &AnemoiVLHTrace<BN254Scalar, 2, 14>,
    input_commitment_trace: &AnemoiVLHTrace<BN254Scalar, 2, 14>,
    folding_witness: &AXfrAddressFoldingWitness,
) -> Result<AXfrPlonkPf> {
    let mut transcript = Transcript::new(OWNERSHIP_PLONK_PROOF_TRANSCRIPT);

    let (mut cs, _) = build_ownership_cs(
        payers_witness,
        nullifier_trace,
        input_commitment_trace,
        &folding_witness,
    );
    let witness = cs.get_and_clear_witness();

    Ok(prover_with_lagrange(
        rng,
        &mut transcript,
        &params.pcs,
        params.lagrange_pcs.as_ref(),
        &params.cs,
        &params.prover_params,
        &witness,
    )?)
}

/// Construct the ownership constraint system.
pub fn build_ownership_cs(
    payer_witness: &PayerWitness,
    nullifier_trace: &AnemoiVLHTrace<BN254Scalar, 2, 14>,
    input_commitment_trace: &AnemoiVLHTrace<BN254Scalar, 2, 14>,
    folding_witness: &AXfrAddressFoldingWitness,
) -> (TurboPlonkCS, usize) {
    let mut cs = TurboCS::new();

    cs.load_anemoi_jive_parameters::<AnemoiJive254>();

    let payers_witnesses_vars = add_payers_witnesses(&mut cs, &[payer_witness]);
    let payer_witness_var = &payers_witnesses_vars[0];

    let keypair = folding_witness.keypair();
    let public_key_scalars = keypair.get_pk().to_bn_scalars().unwrap();
    let secret_key_scalars = keypair.get_sk().to_bn_scalars().unwrap();

    let public_key_scalars_vars = [
        cs.new_variable(public_key_scalars[0]),
        cs.new_variable(public_key_scalars[1]),
        cs.new_variable(public_key_scalars[2]),
    ];
    let secret_key_scalars_vars = [
        cs.new_variable(secret_key_scalars[0]),
        cs.new_variable(secret_key_scalars[1]),
    ];

    let pow_2_128 = BN254Scalar::from(u128::MAX).add(&BN254Scalar::one());
    let zero = BN254Scalar::zero();
    let one = BN254Scalar::one();
    let zero_var = cs.zero_var();
    let mut root_var: Option<VarIndex> = None;

    let key_type = match keypair.get_sk() {
        SecretKey::Ed25519(_) => cs.new_variable(BN254Scalar::one()),
        SecretKey::Secp256k1(_) => cs.new_variable(BN254Scalar::zero()),
    };

    // commitments
    let com_abar_in_var = commit_in_cs(
        &mut cs,
        payer_witness_var.blind,
        payer_witness_var.amount,
        payer_witness_var.asset_type,
        key_type,
        &public_key_scalars_vars,
        input_commitment_trace,
    );

    // prove pre-image of the nullifier
    // 0 <= `amount` < 2^128, so we can encode (`uid`||`amount`) to `uid` * 2^128 + `amount`
    let uid_amount = cs.linear_combine(
        &[
            payer_witness_var.uid,
            payer_witness_var.amount,
            zero_var,
            zero_var,
        ],
        pow_2_128,
        one,
        zero,
        zero,
    );
    let nullifier_var = nullify_in_cs(
        &mut cs,
        &secret_key_scalars_vars,
        uid_amount,
        payer_witness_var.asset_type,
        key_type,
        &public_key_scalars_vars,
        nullifier_trace,
    );

    // Merkle path authentication
    let acc_elem = AccElemVars {
        uid: payer_witness_var.uid,
        commitment: com_abar_in_var,
    };

    let mut path_traces = Vec::new();
    let (commitment, _) = commit(
        &keypair.get_pk(),
        payer_witness.blind,
        payer_witness.amount,
        payer_witness.asset_type,
    )
    .unwrap();
    let leaf_trace = AnemoiJive254::eval_variable_length_hash_with_trace(&[
        BN254Scalar::from(payer_witness.uid),
        commitment,
    ]);
    for (i, mt_node) in payer_witness.path.nodes.iter().enumerate() {
        let trace = AnemoiJive254::eval_jive_with_trace(
            &[mt_node.left, mt_node.mid],
            &[mt_node.right, ANEMOI_JIVE_BN254_SALTS[i]],
        );
        path_traces.push(trace);
    }

    let tmp_root_var = compute_merkle_root_variables(
        &mut cs,
        acc_elem,
        &payer_witness_var.path,
        &leaf_trace,
        &path_traces,
    );

    if let Some(root) = root_var {
        cs.equal(root, tmp_root_var);
    } else {
        root_var = Some(tmp_root_var);
    }

    // prepare public inputs variables
    cs.prepare_pi_variable(nullifier_var);
    cs.prepare_pi_variable(root_var.unwrap()); // safe unwrap

    cs.prepare_pi_variable(payer_witness_var.amount);
    cs.prepare_pi_variable(payer_witness_var.asset_type);

    match folding_witness {
        AXfrAddressFoldingWitness::Secp256k1(a) => prove_address_folding_in_cs_secp256k1(
            &mut cs,
            &public_key_scalars_vars,
            &secret_key_scalars_vars,
            a,
        )
        .unwrap(),
        AXfrAddressFoldingWitness::Ed25519(a) => prove_address_folding_in_cs_ed25519(
            &mut cs,
            &public_key_scalars_vars,
            &secret_key_scalars_vars,
            a,
        )
        .unwrap(),
    }

    // pad the number of constraints to power of two
    cs.pad();

    let n_constraints = cs.size;
    (cs, n_constraints)
}
