use algebra::prelude::AlgebraError;
use ark_bulletproofs::{r1cs::R1CSError as ArkR1CSError, ProofError as ArkProofError};
use ark_std::{boxed::Box, error, fmt, format};
use bulletproofs::{r1cs::R1CSError, ProofError};
use crypto::errors::CryptoError;
use plonk::errors::PlonkError;

pub(crate) type Result<T> = core::result::Result<T, Error>;

#[derive(Debug, Clone, Eq, PartialEq)]
#[allow(missing_docs)]
pub enum Error {
    Algebra(AlgebraError),
    Crypto(CryptoError),
    Plonk(PlonkError),
    R1CS(R1CSError),
    Bulletproofs(ProofError),
    ArkR1CS(ArkR1CSError),
    ArkBulletproofs(ArkProofError),
    ParameterError,
    SignatureError,
    SerializationError,
    DeserializationError,
    DecompressElementError,
    AXfrProverParamsError,
    AXfrVerifierParamsError,
    AXfrVerificationError,
    AXfrProofError,
    AnonFeeProofError,
    XfrCreationAssetAmountError,
    CommitmentInputError,
    CommitmentVerificationError,
    EncryptionError,
    DecryptionError,
    InconsistentStructureError,
    MissingVerifierParamsError,
    MissingURSError,
    MissingSRSError,
    BogusAssetTracerMemo,
    AssetTracingExtractionError,
    XfrVerifyAssetAmountError,
    XfrVerifyAssetTracingAssetAmountError,
    XfrVerifyAssetTracingIdentityError,
    XfrVerifyConfidentialAmountError,
    RangeProofProveError,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Error::*;
        f.write_str(match self {
            Algebra(e) => Box::leak(format!("Algebra: {}", e).into_boxed_str()),
            Crypto(e) => Box::leak(format!("Crypto: {}", e).into_boxed_str()),
            Plonk(e) => Box::leak(format!("Plonk: {}", e).into_boxed_str()),
            R1CS(e) => Box::leak(format!("R1CS: {}", e).into_boxed_str()),
            Bulletproofs(e) => Box::leak(format!("Bulletproofs: {}", e).into_boxed_str()),
            ArkR1CS(e) => Box::leak(format!("Ark R1CS: {}", e).into_boxed_str()),
            ArkBulletproofs(e) => Box::leak(format!("ArkBulletproofs: {}", e).into_boxed_str()),
            ParameterError => "Unexpected parameter for method or function",
            SignatureError => "Signature verification failed",
            SerializationError => "Could not serialize object",
            DeserializationError => "Could not deserialize object",
            DecompressElementError => "Could not decompress group Element",
            AXfrProverParamsError => "Could not preprocess anonymous transfer prover",
            AXfrVerifierParamsError => "Could not preprocess anonymous transfer verifier",
            AXfrVerificationError => "Invalid AXfrBody for merkle root",
            AXfrProofError => "Could not create anonymous transfer proof",
            AnonFeeProofError => "Could not create anonymous transfer proof",
            XfrCreationAssetAmountError => "Invalid total amount per asset in non confidential asset transfer",
            CommitmentInputError => "The number of messages to be committed is invalid",
            CommitmentVerificationError => "Commitment verification failed",
            EncryptionError => "Ciphertext encryption failed",
            DecryptionError => "Ciphertext failed authentication verification",
            InconsistentStructureError => "Crypto Structure is inconsistent",
            MissingVerifierParamsError => "The program is loading verifier parameters that are not hardcoded. Such parameters must be created first",
            MissingURSError => "The Crypto library is compiled without URS. Such parameters must be created first",
            MissingSRSError => "The Crypto library is compiled without SRS, which prevents proof generation",
            BogusAssetTracerMemo => "AssetTracerMemo decryption yields inconsistent data, try brute force decoding",
            AssetTracingExtractionError => "Cannot extract correct data from tracing ciphertext",
            XfrVerifyAssetAmountError => "Invalid total amount per asset in non confidential asset transfer",
            XfrVerifyAssetTracingAssetAmountError => "Asset Tracking error. Asset commitment and asset ciphertext do not match",
            XfrVerifyAssetTracingIdentityError => "Asset Tracking error. Identity reveal proof does not hold",
            XfrVerifyConfidentialAmountError => "Invalid amount in non confidential asset transfer",
            RangeProofProveError => "Could not create range proof due to incorrect input or parameters"
        })
    }
}

impl error::Error for Error {
    #[cfg(feature = "std")]
    fn description(&self) -> &str {
        Box::leak(format!("{}", self).into_boxed_str())
    }
}

impl From<AlgebraError> for Error {
    fn from(e: AlgebraError) -> Error {
        Error::Algebra(e)
    }
}

impl From<CryptoError> for Error {
    fn from(e: CryptoError) -> Error {
        Error::Crypto(e)
    }
}

impl From<PlonkError> for Error {
    fn from(e: PlonkError) -> Error {
        Error::Plonk(e)
    }
}

impl From<R1CSError> for Error {
    fn from(e: R1CSError) -> Error {
        Error::R1CS(e)
    }
}

impl From<ProofError> for Error {
    fn from(e: ProofError) -> Error {
        Error::Bulletproofs(e)
    }
}

impl From<ArkR1CSError> for Error {
    fn from(e: ArkR1CSError) -> Error {
        Error::ArkR1CS(e)
    }
}

impl From<ArkProofError> for Error {
    fn from(e: ArkProofError) -> Error {
        Error::ArkBulletproofs(e)
    }
}
