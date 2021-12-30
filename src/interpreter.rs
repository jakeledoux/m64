use std::collections::HashMap;

use crate::ast::*;

type LabelMap<'a> = HashMap<Label<'a>, usize>;

// TODO: Don't panic, change computer status
macro_rules! arg_panic {
    ($instruction:expr, $arguments:expr) => {
        panic!(
            "Invalid arguments for opcode {:#?}: {:#?}!",
            $instruction, $arguments
        )
    };
}

fn log<T: std::fmt::Debug>(program_counter: usize, value: T) {
    println!("LOG @{} -> {:#?}", program_counter, value)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Ready,
    Error,
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
        matches!(self, Self::Finished) || matches!(self, Self::Error)
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
        matches!(self, Self::Error)
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
    fn read(&self, memory: &Memory) -> u16;
}

trait Write: Read {
    fn write(&self, memory: &mut Memory, value: u16);
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
    fn read(&self, _: &Memory) -> u16 {
        self.value()
    }
}

impl Read for Register {
    fn read(&self, memory: &Memory) -> u16 {
        memory.registers[self.index]
    }
}

impl Read for Address {
    fn read(&self, memory: &Memory) -> u16 {
        let address = match self {
            literal @ Address::IntLiteral(..) => literal.read(memory),
            Address::Register(register) => register.read(memory),
        };
        memory.ram[address as usize]
    }
}

impl Write for Register {
    fn write(&self, memory: &mut Memory, value: u16) {
        memory.registers[self.index] = value;
    }
}

impl Write for Address {
    fn write(&self, memory: &mut Memory, value: u16) {
        let address = match self {
            literal @ Address::IntLiteral(..) => literal.read(memory),
            Address::Register(register) => register.read(memory),
        };
        memory.ram[address as usize] = value;
    }
}

pub struct Stack {
    content: [u16; 10], // todo
    pointer: usize,
}

impl Default for Stack {
    fn default() -> Self {
        let content = Default::default();
        Self {
            content,
            pointer: content.len(),
        }
    }
}

impl Stack {
    pub fn push(&mut self, value: u16) -> Result<(), ()> {
        if self.pointer > 0 {
            self.pointer -= 1;
            self.content[self.pointer] = value;
            Ok(())
        } else {
            Err(())
        }
    }

    pub fn pop(&mut self) -> Option<u16> {
        (self.pointer < self.content.len()).then(|| {
            let value = self.content[self.pointer];
            self.pointer += 1;
            value
        })
    }
}

#[derive(Default)]
pub struct Memory {
    accumulator: u16,
    registers: [u16; 16],
    stack: Stack,
    ram: [u16; 10], // todo: increase
    comparitor: Comparison,
}

#[allow(unused)]
#[derive(Default)]
pub struct Computer<'a> {
    program_counter: usize,
    labels: LabelMap<'a>,
    statements: Vec<Statement<'a>>,
    memory: Memory,
    status: Status,
}

impl<'a> Computer<'a> {
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
                        arg_panic!(opcode, arguments)
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
                        self.memory.stack.push(value).expect("stack overflow");
                    } else {
                        arg_panic!(opcode, arguments)
                    }
                }
                Opcode::POP => {
                    // POP [dest: dyn write]
                    if let Some(dest) = arguments.get(0).as_write() {
                        let value = self.memory.stack.pop().expect("stack underflow");
                        dest.write(&mut self.memory, value);
                    } else {
                        arg_panic!(opcode, arguments)
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
                        arg_panic!(opcode, arguments)
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
                        arg_panic!(opcode, arguments)
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
                        arg_panic!(opcode, arguments)
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
                        arg_panic!(opcode, arguments)
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
                        arg_panic!(opcode, arguments)
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
                        arg_panic!(opcode, arguments)
                    }
                }
                Opcode::RUN => {
                    match &arguments[..] {
                        // RUN [dest: label]
                        [Argument::Label(label)] => {
                            // lower 16 bits of PC
                            self.memory
                                .stack
                                .push((self.program_counter & 0xFFFF) as u16)
                                .expect("stack overflow");
                            // upper 16 bits of PC
                            self.memory
                                .stack
                                .push((self.program_counter >> 16) as u16)
                                .expect("stack overflow");
                            self.program_counter = self.labels[label];
                        }
                        _ => arg_panic!(opcode, arguments),
                    }
                }
                Opcode::RET => {
                    // recombine PC from stack
                    let program_counter =
                        (((self.memory.stack.pop().expect("stack underflow") as u32) << 16)
                            | self.memory.stack.pop().expect("stack underflow") as u32)
                            as usize;
                    self.program_counter = program_counter;
                }
                Opcode::YLD => {
                    self.status = Status::Yield;
                }
                Opcode::JMP => {
                    match &arguments[..] {
                        // JMP [dest: label]
                        [Argument::Label(label)] => {
                            self.program_counter = self.labels[label];
                        }
                        _ => arg_panic!(opcode, arguments),
                    }
                }
                Opcode::JLT => {
                    match &arguments[..] {
                        // JLT [dest: label]
                        [Argument::Label(label)] => {
                            if self.memory.comparitor.is_less() {
                                self.program_counter = self.labels[label];
                            }
                        }
                        _ => arg_panic!(opcode, arguments),
                    }
                }
                Opcode::JGT => {
                    match &arguments[..] {
                        // JLT [dest: label]
                        [Argument::Label(label)] => {
                            if self.memory.comparitor.is_greater() {
                                self.program_counter = self.labels[label];
                            }
                        }
                        _ => arg_panic!(opcode, arguments),
                    }
                }
                Opcode::JEQ => {
                    match &arguments[..] {
                        // JEQ [dest: label]
                        [Argument::Label(label)] => {
                            if self.memory.comparitor.is_equal() {
                                self.program_counter = self.labels[label];
                            }
                        }
                        _ => arg_panic!(opcode, arguments),
                    }
                }
                Opcode::JNE => {
                    match &arguments[..] {
                        // JNE [dest: label]
                        [Argument::Label(label)] => {
                            if self.memory.comparitor.is_not_equal() {
                                self.program_counter = self.labels[label];
                            }
                        }
                        _ => arg_panic!(opcode, arguments),
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
}
