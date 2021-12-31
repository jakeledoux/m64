use ast::File;
use from_pest::FromPest;
use masm::{MASMParser, Rule};
use pest::Parser;

pub mod ast;
pub mod interpreter;
mod masm {
    use pest_derive::Parser;

    #[derive(Parser)]
    #[grammar = "masm.pest"]
    pub struct MASMParser;
}

pub fn parse_str(src: &str) -> Result<File, pest::error::Error<Rule>> {
    let mut parse_tree = MASMParser::parse(Rule::file, src)?;
    Ok(File::from_pest(&mut parse_tree).expect("Failed after parse. PEST may have a bug."))
}

#[cfg(test)]
mod test {
    use crate::{interpreter::Computer, parse_str};

    #[test]
    fn test_parse() {
        let sample_file = include_str!("../samples/sample.masm");
        parse_str(sample_file).unwrap();

        let failure_file = include_str!("../samples/bad_syntax.masm");
        assert!(parse_str(failure_file).is_err());
    }

    #[test]
    fn test_entry_point() {
        let mut computer = execute_program(include_str!("../samples/entry_point.masm"));
        assert_eq!(computer.read_all(), vec![1]);
    }

    #[test]
    fn test_output() {
        let mut computer = execute_program(include_str!("../samples/fib.masm"));
        assert!(computer.status().is_finished());
        assert_eq!(
            computer.read_all(),
            vec![1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]
        );
    }

    fn execute_program(program: &str) -> Computer {
        let program = parse_str(program).unwrap();
        let mut computer = Computer::default();
        computer.load_program(program);
        computer.execute();
        computer
    }
}
