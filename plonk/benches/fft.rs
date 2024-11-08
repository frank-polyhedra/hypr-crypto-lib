use algebra::{bn254::BN254Scalar, prelude::*};
use criterion::{criterion_group, criterion_main, Criterion};
use plonk::poly_commit::field_polynomial::FpPolynomial;

fn bench_fft(c: &mut Criterion) {
    let mut prng = test_rng();
    let n = 65536;

    let mut coefs = Vec::with_capacity(n);
    for _ in 0..n {
        coefs.push(BN254Scalar::random(&mut prng));
    }
    let polynomial = FpPolynomial::from_coefs(coefs);

    let domain = FpPolynomial::<BN254Scalar>::evaluation_domain(n).unwrap();
    let fft = polynomial.fft_with_domain(&domain);
    assert_eq!(polynomial, FpPolynomial::ifft_with_domain(&domain, &fft));

    let mut fft_group = c.benchmark_group("bench_fft");
    fft_group.bench_function("fft".to_string(), |b| {
        b.iter(|| polynomial.fft_with_domain(&domain));
    });

    fft_group.bench_function("ifft".to_string(), |b| {
        b.iter(|| FpPolynomial::ifft_with_domain(&domain, &fft));
    });
    fft_group.finish();
}

criterion_group!(benches, bench_fft);
criterion_main!(benches);
