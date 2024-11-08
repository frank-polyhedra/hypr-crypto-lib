use crate::poly_commit::pcs::ToBytes;
use algebra::prelude::*;
use merlin::Transcript;

/// The trait for polynomial commitment transcript.
pub trait PolyComTranscript {
    /// Append the commitment to the transcript.
    fn append_commitment<C: ToBytes>(&mut self, commitment: &C);

    /// Append the field to the transcript.
    fn append_field_elem<F: Scalar>(&mut self, point: &F);

    /// Get challenge result.
    fn get_challenge_field_elem<F: Scalar>(&mut self, label: &'static [u8]) -> F;
}

impl PolyComTranscript for Transcript {
    fn append_commitment<C: ToBytes>(&mut self, commitment: &C) {
        self.append_message(b"append commitment", &commitment.to_bytes());
    }

    fn append_field_elem<F: Scalar>(&mut self, field_elem: &F) {
        self.append_message(b"append field point", &field_elem.to_bytes());
    }

    fn get_challenge_field_elem<F: Scalar>(&mut self, label: &'static [u8]) -> F {
        let mut buff = [0u8; 32];
        self.challenge_bytes(label, &mut buff[..]);
        F::random(&mut rand_chacha::ChaChaRng::from_seed(buff))
    }
}
