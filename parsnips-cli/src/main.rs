#![deny(
    clippy::alloc_instead_of_core,
    clippy::allow_attributes_without_reason,
    // TODO: enable this when clippy hits 1.66.0
    // clippy::as_ptr_cast_mut,
    clippy::cast_possible_truncation,
    clippy::dbg_macro,
    clippy::equatable_if_let,
    clippy::filter_map_next,
    clippy::flat_map_option,
    clippy::map_unwrap_or,
    clippy::missing_panics_doc,
    clippy::option_if_let_else,
    clippy::panic,
    clippy::std_instead_of_alloc,
    clippy::std_instead_of_core,
    clippy::todo,
    clippy::wildcard_enum_match_arm,
    clippy::wildcard_imports,
    macro_use_extern_crate,
    // TODO: enable this when things are stable
    // missing_docs,
    unused_crate_dependencies,
    unused_extern_crates,
    unused_lifetimes,
    unused_qualifications,
)]

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
