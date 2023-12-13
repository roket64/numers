macro_rules! impl_test_usize {
    ($($test_mod: ident),+) => {$(
        #[cfg(test)]
        mod $test_mod {
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
                todo!()
            }

            #[test]
            fn test_modular_mul() {
                todo!()
            }

            #[test]
            fn test_modular_pow() {
                todo!()
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
    )+};
}

impl_test_usize!(usize, u32, u64, u128);