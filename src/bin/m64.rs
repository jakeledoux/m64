use std::{fs::read_to_string, path::PathBuf};

use clap::{AppSettings, Parser, Subcommand};
use eyre::{bail, Context, Result};
use m64::{
    asm::msize,
    interpreter::{Computer64, Status},
    parse_str,
};

#[derive(Parser, Debug)]
#[clap(name = "m64")]
#[clap(about, version)]
struct Cli {
    #[clap(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Run a program
    #[clap(setting(AppSettings::ArgRequiredElseHelp))]
    Run {
        /// The programs to run
        #[clap(required = true, parse(from_os_str))]
        files: Vec<PathBuf>,
        /// Print computer output to stdout
        #[clap(long, short)]
        print_output: bool,
        /// Use stdin for computer input
        #[clap(long, short)]
        read_input: bool,
    },
    /// Check a program for syntax errors
    #[clap(setting(AppSettings::ArgRequiredElseHelp))]
    Check {
        /// The programs to check
        #[clap(required = true, parse(from_os_str))]
        files: Vec<PathBuf>,
    },
}

fn stdin_provider() -> Option<msize> {
    let mut buf = String::new();
    std::io::stdin()
        .read_line(&mut buf)
        .ok()
        .and_then(|_| buf.trim().parse().ok())
}

/// M64 ASM interpreter CLI
fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Command::Run {
            files,
            print_output,
            read_input,
        } => {
            for file in files {
                let file_content =
                    read_to_string(&file).wrap_err(format!("failed to read file: {:?}", file))?;

                let program =
                    parse_str(&file_content).wrap_err(format!("syntax error in {:?}", file))?;

                let mut computer = Computer64::default();
                computer.load_program(program);

                if print_output {
                    computer.subscribe(|v| println!("{}", v));
                }

                if read_input {
                    computer.provide(stdin_provider);
                }

                if let Status::Error(error) = computer.execute() {
                    bail!("{0:?} on line {1}: {0}", error, computer.program_counter());
                }
            }
        }
        Command::Check { files } => {
            for file in files {
                let file_content =
                    read_to_string(&file).wrap_err(format!("failed to read file: {:?}", file))?;
                parse_str(&file_content).wrap_err(format!("syntax error in {:?}", file))?;
            }
        }
    }
    Ok(())
}
