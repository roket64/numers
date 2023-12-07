use std::fs::File;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::{env, io};

use rayon::prelude::*;

fn read_primes() -> Vec<Vec<u32>> {
    let primes_path: Vec<_> = (1..=50)
        .map(|i| {
            PathBuf::from(format!(
                "{}\\public\\primes\\primes{}",
                env::current_dir().unwrap().display(),
                i
            ))
            .with_extension("txt")
        })
        .collect();

    primes_path
        .par_iter()
        .map(|path| {
            let mut buf = String::new();
            io::BufReader::new(File::open(path).unwrap())
                .read_to_string(&mut buf)
                .unwrap();

            buf.trim()
                .split_whitespace()
                .filter_map(|s| s.parse().ok())
                .collect::<Vec<u32>>()
        })
        .collect::<Vec<Vec<u32>>>()
}
