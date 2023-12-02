use std::fs::File;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

use rayon::prelude::*;

macro_rules! impl_read_vec {
    ($($t: ty, $id: ident);+) => {$(
        pub fn $id(path: &Path) -> io::Result<Vec<$t>> {
            let mut buf = String::new();
            io::BufReader::new(File::open(path).unwrap())
                .read_to_string(&mut buf)
                .unwrap();

            let res: Vec<$t> = buf
                .trim()
                .split_whitespace()
                .filter_map(|item| item.parse::<$t>().ok())
                .collect();
            Ok(res)
        }
    )+};
}

macro_rules! impl_write_vec {
    ($($t: ty, $id: ident);+) => {$(
        pub fn $id(path: &Path, contents: &Vec<$t>) -> io::Result<()> {
            contents
                .chunks(10)
                .map(|ch| {
                    let line = ch
                        .iter()
                        .map(|&i| i.to_string())
                        .collect::<Vec<String>>()
                        .join(" ");
                    line
                })
                .for_each(|line| {
                    File::create(path)
                        .unwrap()
                        .write_all(format!("{}\n", line).as_bytes())
                        .unwrap();
                });

            Ok(())
        }
    )+};
}

impl_read_vec!(isize, read_isizev;
               i32, read_i32v;
               i64, read_i64v;
               i128, read_i128v;
               usize, read_usizev;
               u32, read_u32v;
               u64, read_u64v;
               u128, read_u128v);

impl_write_vec!(isize, write_isizev;
                i32, write_i32v;
                i64, write_i64v;
                i128, write_i128v;
                usize, write_usize;
                u32, write_u32v;
                u64, write_u64v);
