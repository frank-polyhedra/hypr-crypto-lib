use algebra::collections::BTreeMap;

/// Parameters for Bulletproofs.
pub mod bulletproofs;

/// Definitions and constructions for prover and verifier parameters.
pub mod params;
pub use params::*;

#[cfg(not(feature = "no_urs"))]
/// The Bulletproofs(over the Curve25519 curve) URS.
pub static BULLETPROOF_CURVE25519_URS: Option<&'static [u8]> = Some(include_bytes!(
    "../../parameters/bulletproof-curve25519-urs.bin"
));

#[cfg(feature = "no_urs")]
/// The Bulletproofs(over the Curve25519 curve) URS.
pub static BULLETPROOF_CURVE25519_URS: Option<&'static [u8]> = None;

#[cfg(not(feature = "no_urs"))]
/// The Bulletproofs(over the Secq256k1 curve) URS.
pub static BULLETPROOF_SECQ256K1_URS: Option<&'static [u8]> = Some(include_bytes!(
    "../../parameters/bulletproof-secq256k1-urs.bin"
));

#[cfg(feature = "no_urs")]
/// The Bulletproofs(over the Zorro curve) URS.
pub static BULLETPROOF_ZORRO_URS: Option<&'static [u8]> = None;

#[cfg(not(feature = "no_urs"))]
/// The Bulletproofs(over the Zorro curve) URS.
pub static BULLETPROOF_ZORRO_URS: Option<&'static [u8]> =
    Some(include_bytes!("../../parameters/bulletproof-zorro-urs.bin"));

#[cfg(feature = "no_urs")]
/// The Bulletproofs(over the Secq256k1 curve) URS.
pub static BULLETPROOF_SECQ256K1_URS: Option<&'static [u8]> = None;

#[cfg(not(feature = "no_srs"))]
/// The SRS.
pub static SRS: Option<&'static [u8]> = Some(include_bytes!("../../parameters/srs-padding.bin"));

#[cfg(feature = "no_srs")]
/// The SRS.
pub static SRS: Option<&'static [u8]> = None;

#[cfg(not(feature = "no_vk"))]
/// The common part of the verifier parameters for anonymous transfer.
pub static ABAR_TO_ABAR_VERIFIER_COMMON_PARAMS: Option<&'static [u8]> =
    Some(include_bytes!("../../parameters/transfer-vk-common.bin"));

#[cfg(feature = "no_vk")]
/// The common part of the verifier parameters for anonymous transfer.
pub static ABAR_TO_ABAR_VERIFIER_COMMON_PARAMS: Option<&'static [u8]> = None;

#[cfg(not(feature = "no_vk"))]
/// The specific part of the verifier parameters for ed25519 anonymous transfer.
pub static ABAR_TO_ABAR_VERIFIER_ED25519_SPECIFIC_PARAMS: Option<&'static [u8]> = Some(
    include_bytes!("../../parameters/transfer-vk-ed25519-specific.bin"),
);

#[cfg(not(feature = "no_vk"))]
/// The specific part of the verifier parameters for secp256k1 anonymous transfer.
pub static ABAR_TO_ABAR_VERIFIER_SECP256K1_SPECIFIC_PARAMS: Option<&'static [u8]> = Some(
    include_bytes!("../../parameters/transfer-vk-secp256k1-specific.bin"),
);

#[cfg(feature = "no_vk")]
/// The specific part of the verifier parameters for ed25519 anonymous transfer.
pub static ABAR_TO_ABAR_VERIFIER_ED25519_SPECIFIC_PARAMS: Option<&'static [u8]> = None;

#[cfg(feature = "no_vk")]
/// The specific part of the verifier parameters for secp256k1 anonymous transfer.
pub static ABAR_TO_ABAR_VERIFIER_SECP256K1_SPECIFIC_PARAMS: Option<&'static [u8]> = None;

#[cfg(not(feature = "no_vk"))]
/// The verifier parameters for transparent to anonymous.
pub static AR_TO_ABAR_VERIFIER_PARAMS: Option<&'static [u8]> =
    Some(include_bytes!("../../parameters/ar-to-abar-vk.bin"));

#[cfg(feature = "no_vk")]
/// The verifier parameters for transparent to anonymous.
pub static AR_TO_ABAR_VERIFIER_PARAMS: Option<&'static [u8]> = None;

#[cfg(not(feature = "no_vk"))]
/// The verifier parameters for ed25519 anonymous to transparent.
pub static OWNERSHIP_ED25519_VERIFIER_PARAMS: Option<&'static [u8]> =
    Some(include_bytes!("../../parameters/ownership-vk-ed25519.bin"));

#[cfg(feature = "no_vk")]
/// The verifier parameters for ed25519 anonymous to transparent.
pub static OWNERSHIP_ED25519_VERIFIER_PARAMS: Option<&'static [u8]> = None;

#[cfg(not(feature = "no_vk"))]
/// The verifier parameters for secp256k1 anonymous to transparent.
pub static OWNERSHIP_SECP256K1_VERIFIER_PARAMS: Option<&'static [u8]> = Some(include_bytes!(
    "../../parameters/ownership-vk-secp256k1.bin"
));

#[cfg(feature = "no_vk")]
/// The verifier parameters for secp256k1 anonymous to transparent.
pub static OWNERSHIP_SECP256K1_VERIFIER_PARAMS: Option<&'static [u8]> = None;

#[cfg(feature = "no_srs")]
lazy_static! {
    /// The Lagrange format of the SRS.
    pub static ref LAGRANGE_BASES: BTreeMap<usize, &'static [u8]> = BTreeMap::default();
}

#[cfg(not(feature = "no_srs"))]
static LAGRANGE_BASE_4096: &[u8] = include_bytes!("../../parameters/lagrange-srs-4096.bin");
#[cfg(all(not(feature = "no_srs"), not(feature = "lightweight")))]
static LAGRANGE_BASE_8192: &[u8] = include_bytes!("../../parameters/lagrange-srs-8192.bin");

#[cfg(not(feature = "no_srs"))]
lazy_static! {
    /// The Lagrange format of the SRS.
    pub static ref LAGRANGE_BASES: BTreeMap<usize, &'static [u8]> = {
        let mut m = BTreeMap::new();
        m.insert(4096, LAGRANGE_BASE_4096);
        #[cfg(not(feature = "lightweight"))]
        {
            m.insert(8192, LAGRANGE_BASE_8192);
        }
        m
    };
}
