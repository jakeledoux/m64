use std::path::PathBuf;

use clap::Parser;
use m64::{
    interpreter::{Computer64, Status},
    masm::msize,
    parse_str,
};

macro_rules! error {
    ($str:literal, $($any:expr),*) => {{
        eprintln!($str, $($any),*);
        return;
    }}
}

#[derive(Parser, Debug)]
#[clap(name = "masm")]
#[clap(about = "An interpreter for the MAXCOM assembly language")]
struct Opts {
    #[clap(required = true, parse(from_os_str))]
    file: PathBuf,
    #[clap(long, short)]
    print_output: bool,
    #[clap(long, short)]
    read_input: bool,
}

fn stdin_provider() -> Option<msize> {
    let mut buf = String::new();
    std::io::stdin()
        .read_line(&mut buf)
        .ok()
        .and_then(|_| buf.trim().parse().ok())
}

/// MASM interpreter CLI
fn main() {
    let opts = Opts::parse();

    // load file
    if let Ok(file) = std::fs::read_to_string(&opts.file) {
        // parse AST
        match parse_str(&file) {
            Ok(syntax_tree) => {
                let mut computer = Computer64::default();
                computer.load_program(syntax_tree);

                if opts.print_output {
                    computer.subscribe(|v| println!("{}", v));
                }

                if opts.read_input {
                    computer.provide(stdin_provider);
                }

                if let Status::Error(error) = computer.execute() {
                    error!("{0:?} on line {1}: {0}", error, computer.program_counter());
                }
            }
            Err(e) => error!("syntax error in {:?}{}", opts.file, e),
        }
    } else {
        error!("failed to read file: {:?}", opts.file)
    }
}
