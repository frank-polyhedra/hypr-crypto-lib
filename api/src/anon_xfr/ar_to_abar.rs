use crate::anon_xfr::{commit, commit_in_cs, AXfrPlonkPf, TurboPlonkCS, MAX_AXFR_MEMO_SIZE};
use crate::errors::{Error, Result};
use crate::keys::{PublicKey, PublicKeyInner};
use crate::parameters::params::ProverParams;
use crate::parameters::params::VerifierParams;
use crate::structs::{
    AnonAssetRecord, AssetType, AxfrOwnerMemo, OpenAnonAssetRecordBuilder, PayeeWitness,
    PayeeWitnessVars,
};
use algebra::{bn254::BN254Scalar, prelude::*};
use crypto::anemoi_jive::{AnemoiJive254, AnemoiVLHTrace};
use digest::{consts::U64, Digest};
use merlin::Transcript;
use plonk::plonk::{constraint_system::TurboCS, prover::prover_with_lagrange, verifier::verifier};

/// The domain separator for transparent-to-anonymous, for the Plonk proof.
const AR_TO_ABAR_PLONK_PROOF_TRANSCRIPT: &[u8] = b"AR to ABAR Plonk Proof";

/// The transparent-to-anonymous note.
#[derive(Debug, Serialize, Deserialize, Eq, Clone, PartialEq)]
pub struct ArToAbarNote {
    /// The input transparent asset amount.
    pub asset: AssetType,
    /// The input transparent asset type.
    pub amount: u128,
    /// The output anonymous asset record.
    pub output: AnonAssetRecord,
    /// The proof that the output matches the input.
    pub proof: AXfrPlonkPf,
    /// memo to hold the blinding factor of commitment
    pub memo: AxfrOwnerMemo,
}

/// Generate the transparent-to-anonymous body.
pub fn gen_ar_to_abar_note<R: CryptoRng + RngCore, D: Digest<OutputSize = U64> + Default>(
    prng: &mut R,
    params: &ProverParams,
    asset: AssetType,
    amount: u128,
    abar_pubkey: &PublicKey,
    hash: D,
) -> Result<ArToAbarNote> {
    // 1. Construct ABAR.
    let oabar = OpenAnonAssetRecordBuilder::new()
        .amount(amount)
        .asset_type(asset)
        .pub_key(abar_pubkey)
        .finalize(prng)?
        .build()?;

    let payee_witness = PayeeWitness {
        amount: oabar.get_amount(),
        blind: oabar.blind,
        asset_type: oabar.asset_type.as_scalar(),
        public_key: *abar_pubkey,
    };

    let (_, output_trace) = commit(
        abar_pubkey,
        oabar.blind,
        oabar.amount,
        oabar.asset_type.as_scalar(),
    )
    .unwrap();

    let mut transcript = Transcript::new(AR_TO_ABAR_PLONK_PROOF_TRANSCRIPT);
    transcript.append_message(b"hash", hash.finalize().as_slice());

    let (mut cs, _) = build_ar_to_abar_cs(payee_witness, &output_trace);
    let witness = cs.get_and_clear_witness();

    let proof = prover_with_lagrange(
        prng,
        &mut transcript,
        &params.pcs,
        params.lagrange_pcs.as_ref(),
        &params.cs,
        &params.prover_params,
        &witness,
    )?;

    let body = ArToAbarNote {
        asset,
        amount,
        output: AnonAssetRecord::from_oabar(&oabar),
        proof,
        memo: oabar.owner_memo.unwrap(),
    };
    Ok(body)
}

/// Verify the transparent-to-anonymous body.
pub fn verify_ar_to_abar_note<D: Digest<OutputSize = U64> + Default>(
    params: &VerifierParams,
    note: &ArToAbarNote,
    hash: D,
) -> Result<()> {
    // Check the memo size.
    if note.memo.size() > MAX_AXFR_MEMO_SIZE {
        return Err(Error::AXfrVerificationError);
    }

    let mut transcript = Transcript::new(AR_TO_ABAR_PLONK_PROOF_TRANSCRIPT);
    transcript.append_message(b"hash", hash.finalize().as_slice());

    let online_inputs: Vec<BN254Scalar> = vec![
        BN254Scalar::from(note.amount),
        note.asset.as_scalar(),
        note.output.commitment,
    ];

    Ok(verifier(
        &mut transcript,
        &params.shrunk_vk,
        &params.shrunk_cs,
        &params.verifier_params,
        &online_inputs,
        &note.proof,
    )?)
}

/// Construct the transparent-to-anonymous constraint system.
pub fn build_ar_to_abar_cs(
    payee_data: PayeeWitness,
    output_trace: &AnemoiVLHTrace<BN254Scalar, 2, 14>,
) -> (TurboPlonkCS, usize) {
    let mut cs = TurboCS::new();
    cs.load_anemoi_jive_parameters::<AnemoiJive254>();

    let ar_amount_var = cs.new_variable(BN254Scalar::from(payee_data.amount));
    cs.prepare_pi_variable(ar_amount_var);
    let ar_asset_var = cs.new_variable(payee_data.asset_type);
    cs.prepare_pi_variable(ar_asset_var);

    let blind = cs.new_variable(payee_data.blind);

    let public_key_scalars = payee_data.public_key.to_bn_scalars().unwrap();
    let public_key_scalars_vars = [
        cs.new_variable(public_key_scalars[0]),
        cs.new_variable(public_key_scalars[1]),
        cs.new_variable(public_key_scalars[2]),
    ];

    let public_key_type = match payee_data.public_key.0 {
        PublicKeyInner::Ed25519(_) => cs.new_variable(BN254Scalar::one()),
        PublicKeyInner::Secp256k1(_) => cs.new_variable(BN254Scalar::zero()),
        PublicKeyInner::EthAddress(_) => unimplemented!(),
    };
    cs.insert_boolean_gate(public_key_type);

    let payee = PayeeWitnessVars {
        amount: ar_amount_var,
        blind,
        asset_type: ar_asset_var,
        public_key_type,
        public_key_scalars: public_key_scalars_vars,
    };

    // commitment
    let com_abar_out_var = commit_in_cs(
        &mut cs,
        payee.blind,
        payee.amount,
        payee.asset_type,
        public_key_type,
        &public_key_scalars_vars,
        output_trace,
    );

    // prepare the public input for the output commitment
    cs.prepare_pi_variable(com_abar_out_var);

    // pad the number of constraints to power of two
    cs.pad();

    let n_constraints = cs.size;
    (cs, n_constraints)
}
