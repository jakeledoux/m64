# m64

> :warning: This crate is in *pre-alpha* and should not be used for any
> purpose at this time.

A MAXCOM 64 personal computer emulator.

# Memory Map

| start  | end    | usage           | byte represents                                            |
|--------|--------|-----------------|------------------------------------------------------------|
| 0x0000 | 0x03E7 | screen contents | index of character in cell                                 |
| 0x03E8 | 0x07CF | screen colors   | 0xFB where F is foreground color and B is background color |
| 0x07D0 | 0x0E9F | character map   | 8 bytes per character, each bit is a pixel, bytes are rows |
| 0x0EA0 | 0x0F9F | program stack   | any data                                                   |

# Instruction set
| opcode | args (undocumented) |
|--------|---------------------|
| MOV    |                     |
| LOG    |                     |
| PSH    |                     |
| POP    |                     |
| ADD    |                     |
| SUB    |                     |
| MUL    |                     |
| DIV    |                     |
| MOD    |                     |
| CMP    |                     |
| RUN    |                     |
| RET    |                     |
| YLD    |                     |
| JMP    |                     |
| JLT    |                     |
| JGT    |                     |
| JEQ    |                     |
| JNE    |                     |
| NOP    |                     |
| HLT    |                     |

# Standard Library

The M64 comes with a standard library of functions that can be called by pushing
the arguments to the stack and executing `CALL {function code}`.

| function name | function code | args...                | returns    |
|---------------|---------------|------------------------|------------|
| print         | 0x00          | null-terminated string |            |
| getch         | 0x01          | block                  | ASCII code |
| time          | 0x02          |                        | timestamp  |
