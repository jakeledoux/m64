use anyhow::Result;
use ast::File;
use from_pest::FromPest;
pub use interpreter::Computer;
use masm::{MASMParser, Rule};
use pest::Parser;

mod ast;
mod interpreter;
mod masm {
    use pest_derive::Parser;

    #[derive(Parser)]
    #[grammar = "masm.pest"]
    pub struct MASMParser;
}

fn parse_str(src: &str) -> Result<File> {
    let mut parse_tree = MASMParser::parse(Rule::file, src)?;
    Ok(File::from_pest(&mut parse_tree).expect("Failed after parse. PEST may have a bug."))
}

// TODO: remove main() and move main.rs -> lib.rs
fn main() {
    let sample_file = include_str!("../samples/fib.masm");
    let syntax_tree = parse_str(sample_file).unwrap();
    let mut computer = Computer::default();

    computer.load_program(syntax_tree);
    while computer.execute_until_yield().is_yield() {
        println!("Yielding...");
    }
    println!("{:?}", computer.status());
}

#[cfg(test)]
mod test {
    use crate::*;

    #[test]
    fn test_parse() -> Result<()> {
        let sample_file = include_str!("../samples/sample.masm");
        parse_str(sample_file)?;

        let failure_file = include_str!("../samples/bad_syntax.masm");
        assert!(parse_str(failure_file).is_err());

        Ok(())
    }

    // TODO: test programs with I/O to ensure correctness
}
