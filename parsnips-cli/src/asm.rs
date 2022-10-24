use std::{
    error::Error,
    fs::{self, read_to_string},
    io::Write,
    path::PathBuf,
};

use anyhow::anyhow;
use parsnips_asm as asm;
use parsnips_parser as parser;

pub fn assemble_bytes(path: PathBuf) -> Result<Vec<u8>, Box<dyn Error>> {
    let source = read_to_string(path).map_err(|e| anyhow!("failed to read source: {}", e))?;
    let ast = parser::parse(&source).map_err(|e| anyhow!("parsing failed: {:#?}", e))?;
    Ok(asm::assemble(ast).map_err(|e| anyhow!("assembly failed: {:#?}", e))?)
}

pub fn assemble(path: PathBuf, out_path: Option<PathBuf>) -> Result<(), Box<dyn Error>> {
    let bytes = assemble_bytes(path.clone())?;
    let out_path = out_path.unwrap_or(path.with_extension(""));
    if out_path == path {
        Err(anyhow!("default output path would overwrite source"))?;
    }
    let mut out_file =
        fs::File::create(out_path).map_err(|e| anyhow!("failed to create output file: {}", e))?;
    out_file
        .write_all(&bytes)
        .map_err(|e| anyhow!("failed to write output file: {}", e))?;
    Ok(())
}
