# M64

> :warning: This crate is in *pre-alpha* and should not be used for any
> purpose at this time.

A MAXCOM 64 personal computer emulator.

# Usage

## M64 assembly interpreter

``` bash
cargo install m64

m64 run my_program.m64
```

Example M64 assembly programs are available in `./samples`.

# Specs

## Literal syntax

| kind                           | usage               |
|--------------------------------|---------------------|
| decimal literal                | 33                  |
| binary literal                 | 0b100001            |
| hex literal                    | 0x21                |
| char literal                   | '!'                 |
| general-purpose registers (16) | X0-XF               |
| memory address                 | *{literal/register} |

## Instruction set
| opcode | args                |
|--------|---------------------|
| MOV    | dest, src           |
| LOG    | src                 |
| PSH    | src                 |
| POP    | dest                |
| ADD    | dest, src           |
| SUB    | dest, src           |
| MUL    | dest, src           |
| DIV    | dest, src           |
| MOD    | dest, src           |
| CMP    | src, src            |
| RUN    | label               |
| RET    |                     |
| YLD    |                     |
| JMP    | label               |
| JLT    | label               |
| JGT    | label               |
| JEQ    | label               |
| JNE    | label               |
| NOP    |                     |
| HLT    |                     |

## Memory Map *(NYI)*

| start  | end    | usage           | byte represents                                            |
|--------|--------|-----------------|------------------------------------------------------------|
| 0x0000 | 0x03E7 | screen contents | index of character in cell                                 |
| 0x03E8 | 0x07CF | screen colors   | 0xFB where F is foreground color and B is background color |
| 0x07D0 | 0x0E9F | character map   | 8 bytes per character, each bit is a pixel, bytes are rows |
| 0x0EA0 | 0x0F9F | program stack   | any data                                                   |

## Standard Library *(NYI)*

The M64 comes with a standard library of functions that can be called by pushing
the arguments to the stack and executing `RUN {function code}`.

| function name | function code | args...                | returns    |
|---------------|---------------|------------------------|------------|
| print         | 0x00          | null-terminated string |            |
| getch         | 0x01          | block                  | ASCII code |
| time          | 0x02          |                        | timestamp  |
