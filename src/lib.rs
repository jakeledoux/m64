use asm::{ASMParser, Rule};
use ast::File;
use from_pest::FromPest;
use pest::Parser;

pub mod ast;
pub mod interpreter;
pub mod asm {
    use pest_derive::Parser;

    #[allow(non_camel_case_types)]
    pub type msize = i64;

    #[derive(Parser)]
    #[grammar = "m64asm.pest"]
    pub struct ASMParser;
}

pub fn parse_str(src: &str) -> Result<File, pest::error::Error<Rule>> {
    let mut parse_tree = ASMParser::parse(Rule::file, src)?;
    Ok(File::from_pest(&mut parse_tree).expect("Failed after parse. PEST may have a bug."))
}

#[cfg(test)]
mod test {
    use crate::{interpreter::Computer64, parse_str};

    #[test]
    fn test_parse() {
        let sample_file = include_str!("../samples/sample.m64");
        parse_str(sample_file).unwrap();

        let failure_file = include_str!("../samples/bad_syntax.m64");
        assert!(parse_str(failure_file).is_err());
    }

    #[test]
    fn test_entry_point() {
        let mut computer = execute_program(include_str!("../samples/entry_point.m64"));
        assert_eq!(computer.read_all(), vec![1]);
    }

    #[test]
    fn test_output() {
        let mut computer = execute_program(include_str!("../samples/fib.m64"));
        assert!(computer.status().is_finished());
        assert_eq!(
            computer.read_all(),
            vec![1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]
        );
    }

    fn execute_program(program: &str) -> Computer64 {
        let program = parse_str(program).unwrap();
        let mut computer = Computer64::default();
        computer.load_program(program);
        computer.execute();
        computer
    }
}
