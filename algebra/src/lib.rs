//! The crate for algebra for the Crypto library, which unifies the interfaces of different curves
#![cfg_attr(not(feature = "std"), no_std)]
#![deny(unused_import_braces, unused_qualifications, trivial_casts)]
#![deny(trivial_numeric_casts)]
#![deny(stable_features, unreachable_pub, non_shorthand_field_patterns)]
#![deny(unused_attributes, unused_imports, unused_mut, missing_docs)]
#![deny(renamed_and_removed_lints, stable_features, unused_allocation)]
#![deny(unused_comparisons, bare_trait_objects, unused_must_use)]
#![doc(html_logo_url = "https://avatars.githubusercontent.com/u/74745723?s=200&v=4")]
#![doc(html_playground_url = "https://play.rust-lang.org")]
#![warn(
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms,
    rust_2021_compatibility
)]
#![allow(
    clippy::op_ref,
    clippy::suspicious_op_assign_impl,
    clippy::upper_case_acronyms
)]

#[macro_use]
extern crate serde_derive;

/// Module for the BLS12-381 curve.
pub mod bls12_381;

/// Module for the BN254 curve.
pub mod bn254;

/// Module for the secq256k1 curve.
pub mod secq256k1;

/// Module for the secp256k1 curve.
pub mod secp256k1;

/// Module for the Jubjub curve.
pub mod jubjub;

/// Module for the BabyJubjub curve.
pub mod baby_jubjub;

/// Module for the Zorro curve.
pub mod zorro;

/// Module for the ed25519 curve used to work with the Zorro curve in address folding.
pub mod ed25519;

/// Module for the Ristretto group.
pub mod ristretto;

/// Module for error handling.
pub mod errors;

/// Module for traits.
pub mod traits;

/// Module for serialization of scalars and group elements.
pub mod serialization;

/// Module for utils.
pub mod utils;

/// Module for prelude.
#[doc(hidden)]
pub mod prelude;

/// Module for test rng.
pub mod rand_helper;

#[doc(hidden)]
pub use ark_std::{
    borrow, cfg_into_iter, cmp, collections, end_timer, error, fmt, hash, io, iter, marker, ops,
    rand, result, start_timer, str, One, UniformRand, Zero,
};

/// Implement serialization and deserialization
#[macro_export]
macro_rules! serialize_deserialize {
    ($t:ident) => {
        impl serde::Serialize for $t {
            fn serialize<S>(&self, serializer: S) -> core::result::Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                if serializer.is_human_readable() {
                    serializer.serialize_str(&b64enc(&self.to_bytes()))
                } else {
                    serializer.serialize_bytes(&self.to_bytes())
                }
            }
        }

        impl<'de> serde::Deserialize<'de> for $t {
            fn deserialize<D>(deserializer: D) -> core::result::Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                let bytes = if deserializer.is_human_readable() {
                    deserializer.deserialize_str(obj_serde::BytesVisitor)?
                } else {
                    deserializer.deserialize_bytes(obj_serde::BytesVisitor)?
                };
                $t::from_bytes(bytes.as_slice()).map_err(serde::de::Error::custom)
            }
        }
    };
}
