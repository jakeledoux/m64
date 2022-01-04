use super::asm::{msize, Rule};
use pest::Span;
use pest_ast::FromPest;

macro_rules! opcodes {
    ($($variant:ident),*) => {
        #[allow(clippy::upper_case_acronyms)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq, FromPest)]
        #[pest_ast(rule(Rule::operation))]
        pub enum Opcode {
            $($variant),*
        }

        impl std::str::FromStr for Opcode {
            type Err = String;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                Ok(match s.to_uppercase().as_str() {
                    $(
                        stringify!($variant) => Self::$variant,
                    )*
                        _ => return Err(format!("'{}' is not a valid value for Instruction", s)),
                })
            }
        }
    }
}

macro_rules! impl_as_integer {
    ($($type:ty),*) => {
        $(
            impl AsIntegerValue for $type {
                fn value(&self) -> msize {
                    self.value
                }
            }
        )*
    }
}

fn str_from_span(span: Span) -> &str {
    span.as_str()
}

fn parse_register_index(span: Span) -> usize {
    usize::from_str_radix(span.as_str(), 16).expect("invalid digits will cause a syntax error")
}

fn parse_hex_literal(span: Span) -> msize {
    msize::from_str_radix(span.as_str().split_at(2).1, 16)
        .expect("invalid digits will cause a syntax error")
}

fn parse_bin_literal(span: Span) -> msize {
    msize::from_str_radix(span.as_str().split_at(2).1, 2)
        .expect("invalid digits will cause a syntax error")
}

fn parse_char_literal(span: Span) -> msize {
    // todo: handle escaped characters like "\n" and "\r"
    span.as_str().trim_matches('\'').chars().next().unwrap() as msize // will not overflow because
                                                                      // only ascii characters will
                                                                      // parse
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, FromPest)]
#[pest_ast(rule(Rule::label))]
pub struct Label<'i> {
    #[pest_ast(outer(with(str_from_span)))]
    pub value: &'i str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, FromPest)]
#[pest_ast(rule(Rule::label_definition))]
pub struct LabelDefinition<'i> {
    pub label: Label<'i>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, FromPest)]
#[pest_ast(rule(Rule::dec_literal))]
pub struct DecLiteral {
    #[pest_ast(outer(with(str_from_span), with(str::parse), with(Result::unwrap)))]
    pub value: msize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, FromPest)]
#[pest_ast(rule(Rule::hex_literal))]
pub struct HexLiteral {
    #[pest_ast(outer(with(parse_hex_literal)))]
    pub value: msize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, FromPest)]
#[pest_ast(rule(Rule::bin_literal))]
pub struct BinLiteral {
    #[pest_ast(outer(with(parse_bin_literal)))]
    pub value: msize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, FromPest)]
#[pest_ast(rule(Rule::char_literal))]
pub struct CharLiteral {
    #[pest_ast(outer(with(parse_char_literal)))]
    pub value: msize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, FromPest)]
#[pest_ast(rule(Rule::int_literal))]
pub enum IntLiteral {
    Dec(DecLiteral),
    Hex(HexLiteral),
    Bin(BinLiteral),
    Char(BinLiteral),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, FromPest)]
#[pest_ast(rule(Rule::register))]
pub struct Register {
    #[pest_ast(inner(with(parse_register_index)))]
    pub index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, FromPest)]
#[pest_ast(rule(Rule::address))]
pub enum Address {
    IntLiteral(IntLiteral),
    Register(Register),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, FromPest)]
#[pest_ast(rule(Rule::argument))]
pub enum Argument<'i> {
    Address(Address),
    IntLiteral(IntLiteral),
    Register(Register),
    Label(Label<'i>),
}

opcodes! {
    // Data processing / IO
    MOV,
    LOG,
    PSH,
    POP,
    OUT,
    INP,

    // Arithmetic
    ADD,
    SUB,
    MUL,
    DIV,
    MOD,

    // Comparisons
    CMP,

    // Control flow
    RUN,
    RET,
    YLD,
    JMP,
    JLT,
    JGT,
    JEQ,
    JNE,

    // Do nothing
    NOP,
    HLT
}

#[derive(Debug, Clone, PartialEq, Eq, FromPest)]
#[pest_ast(rule(Rule::instruction))]
pub struct Instruction<'i> {
    #[pest_ast(inner(with(str_from_span), with(str::parse), with(Result::unwrap)))]
    pub opcode: Opcode,
    pub arguments: Vec<Argument<'i>>,
}

#[derive(Debug, Clone, PartialEq, Eq, FromPest)]
#[pest_ast(rule(Rule::statement))]
pub enum Statement<'i> {
    LabelDefinition(LabelDefinition<'i>),
    Instruction(Instruction<'i>),
}

#[derive(Debug, Clone, PartialEq, Eq, FromPest)]
#[pest_ast(rule(Rule::file))]
pub struct File<'i> {
    pub statements: Vec<Statement<'i>>,
}

pub trait AsIntegerValue {
    fn value(&self) -> msize;
}

impl_as_integer!(DecLiteral, BinLiteral, HexLiteral, CharLiteral);

impl AsIntegerValue for IntLiteral {
    fn value(&self) -> msize {
        match self {
            IntLiteral::Dec(literal) => literal.value(),
            IntLiteral::Hex(literal) => literal.value(),
            IntLiteral::Bin(literal) => literal.value(),
            IntLiteral::Char(literal) => literal.value(),
        }
    }
}
