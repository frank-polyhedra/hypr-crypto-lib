use crate::{
    keys::{KeyPair, PublicKey, SecretKey, Signature},
    structs::{AssetType, ASSET_TYPE_LENGTH},
};
use algebra::prelude::*;
use serde::Serializer;

type Result<T> = core::result::Result<T, AlgebraError>;

impl FromToBytes for AssetType {
    fn to_bytes(&self) -> Vec<u8> {
        self.0.to_vec()
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != ASSET_TYPE_LENGTH {
            Err(AlgebraError::DeserializationError)
        } else {
            let mut array = [0u8; ASSET_TYPE_LENGTH];
            array.copy_from_slice(bytes);
            Ok(AssetType(array))
        }
    }
}

serialize_deserialize!(SecretKey);

serialize_deserialize!(PublicKey);

serialize_deserialize!(KeyPair);

serialize_deserialize!(Signature);
