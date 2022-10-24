use std::{
    error::Error,
    io::{stdout, Write},
    path::PathBuf,
};

use anyhow::anyhow;

use parsnips_emu as emu;

use crate::asm::assemble_bytes;

pub fn run(path: PathBuf) -> Result<(), Box<dyn Error>> {
    let mut bytes = assemble_bytes(path)?;
    let mut emu = emu::Emulator::new();
    loop {
        match emu.step(bytes.as_mut_slice()) {
            Err(e) => {
                Err(anyhow!("error while running program: {:#?}", e))?;
            }
            Ok(true) => match emu.get_reg(2) {
                1 => {
                    // print integer
                    println!("{}", emu.get_reg(4));
                }
                4 => {
                    // print null-terminated string
                    let s = &bytes[emu.get_reg(4) as usize..];
                    stdout().write_all(
                        &s[..s
                            .iter()
                            .enumerate()
                            .find(|(_, b)| **b == '\0' as u8)
                            .map(|(i, _)| i)
                            .unwrap_or(s.len())],
                    )?;
                }
                10 => {
                    // exit
                    return Ok(());
                }
                u => {
                    Err(anyhow!("unknown syscall: {}", u))?;
                }
            },
            Ok(false) => {}
        }
    }
}
