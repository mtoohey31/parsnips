#![deny(clippy::cast_possible_truncation)]

use std::path::PathBuf;

use clap::{Parser, Subcommand};

mod asm;
mod run;
use asm::assemble;
use run::run;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(subcommand)]
    action: Action,
}

#[derive(Subcommand)]
enum Action {
    #[clap(about = "Assemble source code into a binary")]
    Asm {
        source: PathBuf,
        #[clap(short)]
        out_path: Option<PathBuf>,
    },
    #[clap(about = "Assemble source code then execute it in the emulator")]
    Run { source: PathBuf },
}

fn main() {
    if let Err(e) = match Args::parse().action {
        Action::Asm { source, out_path } => assemble(source, out_path),
        Action::Run { source } => run(source),
    } {
        eprintln!("\x1b[1;31m{}\x1b[1;0m", e);
        std::process::exit(1);
    }
}
