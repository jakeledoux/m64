use std::collections::HashMap;

use crate::{ast::*, masm::msize};
use thiserror::Error;

const STACK_SIZE: usize = 256;
const RAM_SIZE: usize = 64_000;

type LabelMap<'a> = HashMap<Label<'a>, usize>;

macro_rules! expect {
    ($expression:expr, $status:expr) => {
        match $expression {
            Ok(value) => {
                $status = Status::Ready;
                Some(value)
            }
            Err(e) => {
                $status = Status::Error(e);
                None
            }
        }
    };
}

fn raise_arg_error(status: &mut Status, opcode: &Opcode, args: &[Argument]) {
    let args: &'static str = Box::leak(Box::new(format!("{:?}", args)));
    *status = Status::Error(Error::ArgumentError {
        opcode: *opcode,
        args,
    });
}

fn log<T: std::fmt::Debug>(program_counter: usize, value: T) {
    println!("LOG @{} -> {:#?}", program_counter, value)
}

#[allow(clippy::enum_variant_names)]
#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    #[error("invalid arguments `{args:?}` for opcode `{opcode:?}`")]
    ArgumentError { opcode: Opcode, args: &'static str },
    #[error("attempted push to full stack")]
    StackOverflowError,
    #[error("attempted read from empty stack")]
    StackUnderflowError,
    #[error("tried to read from empty input buffer")]
    InputError,
    #[error("attempted to use undefined label {0:?}")]
    UndefinedLabelError(&'static str),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Ready,
    Error(Error),
    Yield,
    Finished,
}

impl Default for Status {
    fn default() -> Self {
        Self::Ready
    }
}

impl Status {
    /// Returns `true` if the status is [`Finished`] or [`Error`].
    ///
    /// [`Finished`]: Status::Finished
    /// [`Error`]: Status::Error
    pub fn is_stopped(&self) -> bool {
        matches!(self, Self::Finished) || matches!(self, Self::Error(_))
    }

    /// Returns `true` if the status is [`Ready`].
    ///
    /// [`Ready`]: Status::Ready
    pub fn is_ready(&self) -> bool {
        matches!(self, Self::Ready)
    }

    /// Returns `true` if the status is [`Yield`].
    ///
    /// [`Yield`]: Status::Yield
    pub fn is_yield(&self) -> bool {
        matches!(self, Self::Yield)
    }

    /// Returns `true` if the status is [`Finished`].
    ///
    /// [`Finished`]: Status::Finished
    pub fn is_finished(&self) -> bool {
        matches!(self, Self::Finished)
    }

    /// Returns `true` if the status is [`Error`].
    ///
    /// [`Error`]: Status::Error
    pub fn is_error(&self) -> bool {
        matches!(self, Self::Error(_))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Comparison {
    Less,
    Equal,
    Greater,
}

impl Default for Comparison {
    fn default() -> Self {
        Self::Equal
    }
}

impl Comparison {
    /// Returns `true` if the comparison is [`Less`].
    ///
    /// [`Less`]: Comparison::Less
    fn is_less(&self) -> bool {
        matches!(self, Self::Less)
    }

    /// Returns `true` if the comparison is not [`Equal`].
    ///
    /// [`Equal`]: Comparison::Equal
    fn is_not_equal(&self) -> bool {
        !matches!(self, Self::Equal)
    }

    /// Returns `true` if the comparison is [`Equal`].
    ///
    /// [`Equal`]: Comparison::Equal
    fn is_equal(&self) -> bool {
        matches!(self, Self::Equal)
    }

    /// Returns `true` if the comparison is [`Greater`].
    ///
    /// [`Greater`]: Comparison::Greater
    fn is_greater(&self) -> bool {
        matches!(self, Self::Greater)
    }
}

impl From<std::cmp::Ordering> for Comparison {
    fn from(ord: std::cmp::Ordering) -> Self {
        match ord {
            std::cmp::Ordering::Less => Self::Less,
            std::cmp::Ordering::Equal => Self::Equal,
            std::cmp::Ordering::Greater => Self::Greater,
        }
    }
}

trait Read {
    fn read(&self, memory: &Memory) -> msize;
}

trait Write: Read {
    fn write(&self, memory: &mut Memory, value: msize);
}

trait AsRead {
    fn as_read(&self) -> Option<&dyn Read>;
}

impl AsRead for Option<&Argument<'_>> {
    fn as_read(&self) -> Option<&dyn Read> {
        self.and_then(|inside| inside.as_read())
    }
}

impl AsRead for Argument<'_> {
    fn as_read(&self) -> Option<&dyn Read> {
        Some(match self {
            Argument::Register(register) => register,
            Argument::Address(address) => address,
            Argument::IntLiteral(literal) => literal,
            _ => return None,
        })
    }
}

trait AsWrite {
    fn as_write(&self) -> Option<&dyn Write>;
}

impl AsWrite for Option<&Argument<'_>> {
    fn as_write(&self) -> Option<&dyn Write> {
        self.and_then(|inside| inside.as_write())
    }
}

impl AsWrite for Argument<'_> {
    fn as_write(&self) -> Option<&dyn Write> {
        Some(match self {
            Argument::Register(register) => register,
            Argument::Address(address) => address,
            _ => return None,
        })
    }
}

impl Read for IntLiteral {
    fn read(&self, _: &Memory) -> msize {
        self.value()
    }
}

impl Read for Register {
    fn read(&self, memory: &Memory) -> msize {
        memory.registers[self.index]
    }
}

impl Read for Address {
    fn read(&self, memory: &Memory) -> msize {
        let address = match self {
            literal @ Address::IntLiteral(..) => literal.read(memory),
            Address::Register(register) => register.read(memory),
        };
        memory.ram[address as usize]
    }
}

impl Write for Register {
    fn write(&self, memory: &mut Memory, value: msize) {
        memory.registers[self.index] = value;
    }
}

impl Write for Address {
    fn write(&self, memory: &mut Memory, value: msize) {
        let address = match self {
            literal @ Address::IntLiteral(..) => literal.read(memory),
            Address::Register(register) => register.read(memory),
        };
        memory.ram[address as usize] = value;
    }
}

pub struct Stack {
    content: [msize; STACK_SIZE],
    pointer: usize,
}

impl Default for Stack {
    fn default() -> Self {
        let content = [0; STACK_SIZE];
        Self {
            content,
            pointer: content.len(),
        }
    }
}

impl Stack {
    pub fn push(&mut self, value: msize) -> Result<(), Error> {
        if self.pointer > 0 {
            self.pointer -= 1;
            self.content[self.pointer] = value;
            Ok(())
        } else {
            Err(Error::StackOverflowError)
        }
    }

    pub fn pop(&mut self) -> Result<msize, Error> {
        if self.pointer < self.content.len() {
            let value = self.content[self.pointer];
            self.pointer += 1;
            Ok(value)
        } else {
            Err(Error::StackUnderflowError)
        }
    }
}

pub struct Memory {
    accumulator: msize,
    registers: [msize; 16],
    stack: Stack,
    ram: [msize; RAM_SIZE],
    comparitor: Comparison,
}

impl Default for Memory {
    fn default() -> Self {
        Self {
            accumulator: Default::default(),
            registers: Default::default(),
            stack: Default::default(),
            ram: [0; RAM_SIZE],
            comparitor: Default::default(),
        }
    }
}

#[derive(Default)]
pub struct BufStream<T> {
    content: Vec<T>,
    subscribers: Vec<Box<dyn Fn(&T)>>,
    provider: Option<Box<dyn Fn() -> Option<T>>>,
}

impl<T: std::fmt::Debug> std::fmt::Debug for BufStream<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.content.fmt(f)
    }
}

impl<T> BufStream<T> {
    pub fn read(&mut self) -> Option<T> {
        let mut value = (!self.content.is_empty()).then(|| self.content.remove(0));
        if let Some(provider) = &self.provider {
            value = value.or_else(provider);
        }
        value
    }

    pub fn read_all(&mut self) -> Vec<T> {
        self.content.drain(..).collect()
    }

    pub fn write(&mut self, value: T) {
        self.subscribers.iter().for_each(|f| f(&value));
        self.content.push(value);
    }

    pub fn write_iter(&mut self, iter: impl IntoIterator<Item = T>) {
        let mut new_content: Vec<T> = iter.into_iter().collect();
        self.subscribers
            .iter()
            .for_each(|f| new_content.iter().for_each(|v| f(v)));
        self.content.append(&mut new_content)
    }

    pub fn subscribe(&mut self, callback: impl Fn(&T) + 'static) {
        self.subscribers.push(Box::new(callback))
    }

    pub fn provide(&mut self, provider: impl Fn() -> Option<T> + 'static) {
        self.provider = Some(Box::new(provider));
    }
}

#[derive(Default)]
pub struct Computer<'a> {
    program_counter: usize,
    labels: LabelMap<'a>,
    statements: Vec<Statement<'a>>,
    memory: Memory,
    status: Status,
    output: BufStream<msize>,
    input: BufStream<msize>,
}

impl<'a> Computer<'a> {
    pub fn status(&self) -> Status {
        self.status
    }

    pub fn program_counter(&self) -> usize {
        self.program_counter
    }

    pub fn load_program(&mut self, program: File<'a>) {
        self.statements = program.statements;
        self.labels = self
            .statements
            .iter()
            .enumerate()
            .filter_map(|(idx, statement)| {
                if let Statement::LabelDefinition(LabelDefinition { label }) = statement {
                    Some((*label, idx))
                } else {
                    None
                }
            })
            .collect();

        if let Some(&start) = self.labels.get(&Label { value: ".start" }) {
            self.program_counter = start;
        }
    }

    pub fn step(&mut self) -> Status {
        if self.status.is_yield() {
            self.status = Status::Ready;
        } else if self.status.is_stopped() {
            return self.status;
        }

        let statement = &self.statements[self.program_counter];
        self.program_counter += 1;
        match statement {
            Statement::Instruction(Instruction { opcode, arguments }) => match opcode {
                Opcode::MOV => {
                    // MOV [dest: dyn write] [src: dyn read]
                    if let (Some(dest), Some(src)) =
                        (arguments.get(0).as_write(), arguments.get(1).as_read())
                    {
                        let value = src.read(&self.memory);
                        dest.write(&mut self.memory, value);
                    } else {
                        raise_arg_error(&mut self.status, opcode, arguments)
                    }
                }
                Opcode::LOG => {
                    for arg in arguments {
                        // LOG [any..]
                        match arg {
                            Argument::Label(label) => log(self.program_counter, self.labels[label]),
                            Argument::IntLiteral(literal) => {
                                log(self.program_counter, literal.read(&self.memory))
                            }
                            Argument::Register(register) => {
                                log(self.program_counter, register.read(&self.memory))
                            }
                            Argument::Address(address) => {
                                log(self.program_counter, address.read(&self.memory))
                            }
                        }
                    }
                }
                Opcode::PSH => {
                    // PSH [src: dyn read]
                    if let Some(src) = arguments.get(0).as_read() {
                        let value = src.read(&self.memory);
                        expect!(self.memory.stack.push(value), self.status);
                    } else {
                        raise_arg_error(&mut self.status, opcode, arguments)
                    }
                }
                Opcode::POP => {
                    // POP [dest: dyn write]
                    if let Some(dest) = arguments.get(0).as_write() {
                        if let Some(value) = expect!(self.memory.stack.pop(), self.status) {
                            dest.write(&mut self.memory, value);
                        }
                    } else {
                        raise_arg_error(&mut self.status, opcode, arguments)
                    }
                }
                Opcode::OUT => {
                    // OUT [src: dyn read]
                    if let Some(src) = arguments.get(0).as_read() {
                        let value = src.read(&self.memory);
                        self.output.write(value);
                    } else {
                        raise_arg_error(&mut self.status, opcode, arguments)
                    }
                }
                Opcode::INP => {
                    // INP [dest: dyn write]
                    if let Some(dest) = arguments.get(0).as_write() {
                        if let Some(value) = self.input.read() {
                            dest.write(&mut self.memory, value);
                        } else {
                            self.status = Status::Error(Error::InputError);
                        }
                    } else {
                        raise_arg_error(&mut self.status, opcode, arguments)
                    }
                }
                Opcode::ADD => {
                    // ADD [dest: dyn write] [src: dyn read]
                    if let (Some(dest), Some(src)) =
                        (arguments.get(0).as_write(), arguments.get(1).as_read())
                    {
                        let value = dest.read(&self.memory) + src.read(&self.memory);
                        dest.write(&mut self.memory, value);
                    }
                    // ADD [src: dyn read]
                    else if let Some(src) = arguments.get(0).as_read() {
                        self.memory.accumulator += src.read(&self.memory);
                    } else {
                        raise_arg_error(&mut self.status, opcode, arguments)
                    }
                }
                Opcode::SUB => {
                    // SUB [dest: dyn write] [src: dyn read]
                    if let (Some(dest), Some(src)) =
                        (arguments.get(0).as_write(), arguments.get(1).as_read())
                    {
                        let value = dest.read(&self.memory) - src.read(&self.memory);
                        dest.write(&mut self.memory, value);
                    }
                    // SUB [src: dyn read]
                    else if let Some(src) = arguments.get(0).as_read() {
                        self.memory.accumulator -= src.read(&self.memory);
                    } else {
                        raise_arg_error(&mut self.status, opcode, arguments)
                    }
                }
                Opcode::MUL => {
                    // MUL [dest: dyn write] [src: dyn read]
                    if let (Some(dest), Some(src)) =
                        (arguments.get(0).as_write(), arguments.get(1).as_read())
                    {
                        let value = dest.read(&self.memory) * src.read(&self.memory);
                        dest.write(&mut self.memory, value);
                    }
                    // MUL [src: dyn read]
                    else if let Some(src) = arguments.get(0).as_read() {
                        self.memory.accumulator *= src.read(&self.memory);
                    } else {
                        raise_arg_error(&mut self.status, opcode, arguments)
                    }
                }
                Opcode::DIV => {
                    // DIV [dest: dyn write] [src: dyn read]
                    if let (Some(dest), Some(src)) =
                        (arguments.get(0).as_write(), arguments.get(1).as_read())
                    {
                        let value = dest.read(&self.memory) / src.read(&self.memory);
                        dest.write(&mut self.memory, value);
                    }
                    // DIV [src: dyn read]
                    else if let Some(src) = arguments.get(0).as_read() {
                        self.memory.accumulator /= src.read(&self.memory);
                    } else {
                        raise_arg_error(&mut self.status, opcode, arguments)
                    }
                }
                Opcode::MOD => {
                    // MOD [dest: dyn write] [src: dyn read]
                    if let (Some(dest), Some(src)) =
                        (arguments.get(0).as_write(), arguments.get(1).as_read())
                    {
                        let value = dest.read(&self.memory) % src.read(&self.memory);
                        dest.write(&mut self.memory, value);
                    }
                    // MOD [src: dyn read]
                    else if let Some(src) = arguments.get(0).as_read() {
                        self.memory.accumulator %= src.read(&self.memory);
                    } else {
                        raise_arg_error(&mut self.status, opcode, arguments)
                    }
                }
                Opcode::CMP => {
                    // CMP [lhs: dyn read] [rhs: dyn read]
                    if let (Some(lhs), Some(rhs)) =
                        (arguments.get(0).as_read(), arguments.get(1).as_read())
                    {
                        self.memory.comparitor =
                            lhs.read(&self.memory).cmp(&rhs.read(&self.memory)).into();
                    } else {
                        raise_arg_error(&mut self.status, opcode, arguments)
                    }
                }
                Opcode::RUN => {
                    match &arguments[..] {
                        // RUN [dest: label]
                        [Argument::Label(label)] => {
                            // lower 16 bits of PC
                            if expect!(
                                self.memory
                                    .stack
                                    .push((self.program_counter & 0xFFFF) as msize),
                                self.status
                            )
                            .is_some()
                            {
                                // upper 16 bits of PC
                                if expect!(
                                    self.memory
                                        .stack
                                        .push((self.program_counter >> 16) as msize),
                                    self.status
                                )
                                .is_some()
                                {
                                    self.program_counter = self.labels[label];
                                }
                            }
                        }
                        _ => raise_arg_error(&mut self.status, opcode, arguments),
                    }
                }
                Opcode::RET => {
                    // recombine PC from stack
                    if let (Some(upper_bits), Some(lower_bits)) = (
                        expect!(self.memory.stack.pop(), self.status),
                        expect!(self.memory.stack.pop(), self.status),
                    ) {
                        let program_counter =
                            (((upper_bits as u32) << 16) | lower_bits as u32) as usize;
                        self.program_counter = program_counter;
                    }
                }
                Opcode::YLD => {
                    self.status = Status::Yield;
                }
                Opcode::JMP => {
                    match &arguments[..] {
                        // JMP [dest: label]
                        [Argument::Label(label)] => {
                            if let Some(&label_ptr) = self.labels.get(label) {
                                self.program_counter = label_ptr;
                            } else {
                                let label: &'static str =
                                    Box::leak(Box::new(label.value.to_string()));
                                self.status = Status::Error(Error::UndefinedLabelError(label));
                                return self.status;
                            }
                        }
                        _ => raise_arg_error(&mut self.status, opcode, arguments),
                    }
                }
                Opcode::JLT => {
                    match &arguments[..] {
                        // JLT [dest: label]
                        [Argument::Label(label)] => {
                            if self.memory.comparitor.is_less() {
                                if let Some(&label_ptr) = self.labels.get(label) {
                                    self.program_counter = label_ptr;
                                } else {
                                    let label: &'static str =
                                        Box::leak(Box::new(label.value.to_string()));
                                    self.status = Status::Error(Error::UndefinedLabelError(label));
                                    return self.status;
                                }
                            }
                        }
                        _ => raise_arg_error(&mut self.status, opcode, arguments),
                    }
                }
                Opcode::JGT => {
                    match &arguments[..] {
                        // JLT [dest: label]
                        [Argument::Label(label)] => {
                            if self.memory.comparitor.is_greater() {
                                if let Some(&label_ptr) = self.labels.get(label) {
                                    self.program_counter = label_ptr;
                                } else {
                                    let label: &'static str =
                                        Box::leak(Box::new(label.value.to_string()));
                                    self.status = Status::Error(Error::UndefinedLabelError(label));
                                    return self.status;
                                }
                            }
                        }
                        _ => raise_arg_error(&mut self.status, opcode, arguments),
                    }
                }
                Opcode::JEQ => {
                    match &arguments[..] {
                        // JEQ [dest: label]
                        [Argument::Label(label)] => {
                            if self.memory.comparitor.is_equal() {
                                if let Some(&label_ptr) = self.labels.get(label) {
                                    self.program_counter = label_ptr;
                                } else {
                                    let label: &'static str =
                                        Box::leak(Box::new(label.value.to_string()));
                                    self.status = Status::Error(Error::UndefinedLabelError(label));
                                    return self.status;
                                }
                            }
                        }
                        _ => raise_arg_error(&mut self.status, opcode, arguments),
                    }
                }
                Opcode::JNE => {
                    match &arguments[..] {
                        // JNE [dest: label]
                        [Argument::Label(label)] => {
                            if self.memory.comparitor.is_not_equal() {
                                if let Some(&label_ptr) = self.labels.get(label) {
                                    self.program_counter = label_ptr;
                                } else {
                                    let label: &'static str =
                                        Box::leak(Box::new(label.value.to_string()));
                                    self.status = Status::Error(Error::UndefinedLabelError(label));
                                    return self.status;
                                }
                            }
                        }
                        _ => raise_arg_error(&mut self.status, opcode, arguments),
                    }
                }
                Opcode::NOP => {}
                Opcode::HLT => self.program_counter = self.statements.len(),
            },
            Statement::LabelDefinition(_) => {}
        }

        if self.program_counter >= self.statements.len() {
            self.status = Status::Finished;
        }

        self.status
    }

    pub fn execute(&mut self) -> Status {
        loop {
            let status = self.step();
            if status.is_stopped() {
                break status;
            }
        }
    }

    pub fn execute_until_yield(&mut self) -> Status {
        while self.step().is_ready() {}
        self.status
    }

    pub fn read(&mut self) -> Option<msize> {
        self.output.read()
    }

    pub fn read_all(&mut self) -> Vec<msize> {
        self.output.read_all()
    }

    pub fn subscribe(&mut self, callback: impl Fn(&msize) + 'static) {
        self.output.subscribe(callback)
    }

    pub fn write(&mut self, value: msize) {
        self.input.write(value)
    }

    pub fn write_iter(&mut self, iter: impl IntoIterator<Item = msize>) {
        self.input.write_iter(iter)
    }

    pub fn provide(&mut self, provider: impl Fn() -> Option<msize> + 'static) {
        self.input.provide(provider)
    }
}
