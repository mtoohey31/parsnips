#![deny(clippy::alloc_instead_of_core)]
#![deny(clippy::allow_attributes_without_reason)]
// TODO: enable this when clippy hits 1.66.0
// #![deny(clippy::as_ptr_cast_mut)]
#![deny(clippy::cast_possible_truncation)]
#![deny(clippy::dbg_macro)]
#![deny(clippy::equatable_if_let)]
#![deny(clippy::filter_map_next)]
#![deny(clippy::flat_map_option)]
#![deny(clippy::map_unwrap_or)]
#![deny(clippy::missing_panics_doc)]
#![deny(clippy::option_if_let_else)]
#![deny(clippy::panic)]
#![deny(clippy::std_instead_of_alloc)]
#![deny(clippy::std_instead_of_core)]
#![deny(clippy::todo)]
#![deny(clippy::wildcard_enum_match_arm)]
#![deny(clippy::wildcard_imports)]
#![deny(macro_use_extern_crate)]
// TODO: enable this when things are stable
// #![deny(missing_docs)]
#![deny(unused_crate_dependencies)]
#![deny(unused_extern_crates)]
#![deny(unused_lifetimes)]
#![deny(unused_qualifications)]

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
