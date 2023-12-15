extern crate numers;

mod io;
#[cfg(test)]
mod isize;
#[cfg(test)]
mod usize;

use rand::{distributions::uniform::SampleUniform, Rng};
use rayon::prelude::*;
use numers::Int;

pub fn gen_random_int(size: usize, lhs: u32, rhs: u32) -> Vec<u32> {
    (0..size)
        .into_iter()
        .map(|_| rand::thread_rng().gen_range(lhs..rhs))
        .collect()
}

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
                rng.gen_range(lhs_range.0..=lhs_range.1),
                rng.gen_range(rhs_range.0..=rhs_range.1),
                rng.gen_range(mod_range.0..=mod_range.1),
            )
        })
        .collect::<Vec<(T, T, T)>>()
}

pub fn test_modular_fn<T, F>(sample: &[(T, T, T)], func: F)
where
    T: Send + Sync,
    F: Fn(&T, &T, &T) + Send + Sync,
{
    sample.into_par_iter().for_each(|(x, y, m)| {
        func(x, y, m);
    })
}
