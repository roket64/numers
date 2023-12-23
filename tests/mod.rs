use numers::Int;
use rand::{distributions::uniform::SampleUniform, Rng};
use rayon::prelude::*;

pub const ITER_SIZE: usize = 1_000;

pub fn gen_modular_sample<T>(
    size: usize,
    lhs_range: (T, T),
    rhs_range: (T, T),
    mod_range: (T, T),
) -> Vec<(T, T, T)>
where
    T: Int + PartialEq + Copy + SampleUniform,
{
    let mut rng = rand::thread_rng();
    (0..size)
        .into_iter()
        .map(|_| {
            (
                // generate random integer on given range, both sides inclusive
                rng.gen_range(lhs_range.0..=lhs_range.1),
                rng.gen_range(rhs_range.0..=rhs_range.1),
                rng.gen_range(mod_range.0..=mod_range.1),
            )
        })
        // is this necessary?
        .collect::<Vec<(T, T, T)>>()
}

#[deprecated]
pub fn test_modular_fn<T, F>(sample: &[(T, T, T)], func: F)
where
    T: Send + Sync,
    F: Fn(&T, &T, &T) + Send + Sync,
{
    sample.into_par_iter().for_each(|(x, y, m)| {
        func(x, y, m);
    })
}

pub fn test_mod_func<T, F>(
    iter: usize,
    lhs_range: (T, T),
    rhs_range: (T, T),
    mod_range: (T, T),
    func: F,
) where
    T: Int + Copy + Send + Sync + SampleUniform,
    F: Fn(&T, &T, &T) + Send + Sync,
{
    (0..iter).into_par_iter().for_each(|_| {
        let mut rng = rand::thread_rng();
        let (x, y, m) = (
            rng.gen_range(lhs_range.0..=lhs_range.1),
            rng.gen_range(rhs_range.0..=rhs_range.1),
            rng.gen_range(mod_range.0..=mod_range.1),
        );
        func(&x, &y, &m);
    })
}

macro_rules! impl_test_usize {
    ($t: ty, $test_mod: ident) => {
        #[cfg(test)]
        mod $test_mod {
            use std::mem;
            use rand::Rng;

            use num_integer::Roots;
            use numers::Int;

            use super::test_mod_func as __test;
            use super::ITER_SIZE as __iter;

            #[test]
            fn test_ext_gcd() {
                todo!()
            }

            #[test]
            fn test_factorize() {
                todo!()
            }

            #[test]
            fn test_modular_add() {
                fn run_rnd_tests() {
                    // none of the each side should not exceed this to prevent overflow
                    let threshold = <$t>::MAX / 2;

                    let lhs_range = (1, rand::random::<$t>() % threshold);
                    let rhs_range = (1, <$t>::MAX - lhs_range.1);
                    let mod_range = (1, <$t>::MAX);

                    // modular_add checker
                    let f = |x: &$t, y: &$t, m: &$t| {
                        // debugger for when the test fails
                        dbg!(x, y, m);
                        // check if the values is in the overflow-safe range
                        assert!(x <= &(<$t>::MAX - y));
                        // check the values are same
                        assert_eq!((x + y) % m, x.modular_add(y, m).unwrap());
                    };

                    // generate random samples numbers of __smpl_sz on given thresholds for each iteration
                    __test(__iter, lhs_range, rhs_range, mod_range, f);
                }

                run_rnd_tests();
            }

            #[test]
            fn test_modular_mul() {
                fn run_rnd_tests() {
                    // none of the each side should not exceed this to prevent overflow
                    let threshold = <$t>::MAX.sqrt();

                    let lhs_range = (1, rand::random::<$t>() % threshold);
                    let rhs_range = (1, <$t>::MAX / lhs_range.1);
                    let mod_range = (1, <$t>::MAX);

                    // modular_mul checker
                    let f = |x: &$t, y: &$t, m: &$t| {
                        // debugger for when the test fails
                        dbg!(x, y, m);
                        // check if the values is in the overflow-safe range
                        assert!(x <= &(<$t>::MAX / y));
                        // check the values are same
                        assert_eq!((x * y) % m, x.modular_mul(y, m).unwrap());
                    };

                    // generate random samples numbers of __smpl_sz on given thresholds for each iteration
                    __test(__iter, lhs_range, rhs_range, mod_range, f);
                }

                run_rnd_tests();
            }

            #[test]
            fn test_modular_pow() {
                fn run_rnd_tests() {
                    let e_threshold = |n: &$t| {
                        let mut e = 2;
                        while let Some(_) = n.checked_pow(e) {
                            e += 1
                        }
                        // e - 1 is actual threshold
                        e - 1
                    };

                    let mut rng = rand::thread_rng();
                    let b_threshold = (mem::size_of::<$t>() * 8) - 3;
                    let b = rng.gen_range(2..b_threshold);
                    let e = e_threshold(&(b as $t));

                    let f = |x: &$t, y: &$t, m: &$t| {
                        // debugger for when the test fails
                        dbg!(x, y, m);
                        // check the values are same
                        assert_eq!(x.pow(*y as u32) % m, x.modular_pow(y, m).unwrap());
                    };

                    (0..__iter).into_iter().for_each(|_|{
                        let rnd_e = rng.gen_range(1..=e);
                        f(&(b as $t), &(rnd_e as $t), &107);
                    })
                }

                run_rnd_tests();
            }

            #[test]
            fn modular_sqrt() {
                todo!()
            }

            #[test]
            fn is_prime() {
                todo!()
            }

            #[test]
            fn test_pi() {
                unimplemented!()
            }

            #[test]
            fn tset_euler_phi() {
                unimplemented!()
            }

            #[test]
            fn test_tau() {
                unimplemented!()
            }

            #[test]
            fn test_sigma() {
                unimplemented!()
            }

            #[test]
            fn test_omega() {
                unimplemented!()
            }

            #[test]
            fn test_jacobi() {
                unimplemented!()
            }
        }
    };
}

impl_test_usize!(usize, test_usize);
impl_test_usize!(u32, test_u32);
impl_test_usize!(u64, test_u64);
impl_test_usize!(u128, test_u128);
