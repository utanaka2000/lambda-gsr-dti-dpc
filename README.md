# lambda-gsr-dti-dpc

**lambda-gsr-dti-dpc** is an implementation of the **dynamic purity check** 
This implementation is based on: 

- lambda-gsr(https://github.com/ymyzk/lambda-gsr)
- lambda-dti(https://github.com/ymyzk/lambda-dti)

## Requirements
- opam 2.0.0+
- OCaml 4.03.0+
- Dune 1.2.0+ (formerly known as Jbuilder)
- Menhir
- OUnit 2 (optional for running unit tests)
- [rlwrap](https://github.com/hanslub42/rlwrap) (optional for line editing and input history)

## Getting started
###  Building from source
```console
$ dune build
$ ./_build/default/bin/main.exe
```
Run `$ ./_build/default/bin/main.exe --help` for command line options.

(Optional) Run the following command to install the application:
```
$ dune install
$ ldti
```

## Tips
### Running tests
```console
$ dune runtest
```



### Non-interactive mode
You can specify a file as a command line argument. Our interpreter executes the programs in the file then exits.
```console
$ ldti ./sample.ldti
```

### Line editing
You may want to use rlwrap for line editing and input history.
```console
$ rlwrap ldti
```

### Top-level
- Let declaration: `let x ... = e;;`
- Recursion declaration: `let rec f x ... = e;;`
- Expression: `e;;`
- Debug mode: `#debug true;;` `#debug false;;`
- Setting reset mode: `#set_reset true;;` `#set_reset false;;`
- Escape interactive mode: `#quit`

### Expressions `e`
- Variables: lowercase alphabet followed by lowercase alphabets, numbers, `_`, or `'`
- Constants:
  - Integers: `0`, `1`, `2`, ...
  - Booleans: `true`, `false`
  - Unit: `()`
- Unary operators for integers: `+`,  `-`
- Binary operators (from higher precedence to lower precedence):
  - Integer multiplication, division (left): `*`, `/` 
  - Integer addition, subtraction (left): `+`, `-`
  - Integer comparators (left): `=`, `<`, `>` 
- Abstraction:
  - Simple: `fun x -> e`
  - Multiple parameters: `fun x y z ... -> e`
  - With type annotations: `fun^U1' (x: U1) y ^U3'(z: U3) ...: U -> e`
- Application: `e1 e2`
- Let expression:
  - Simple: `let x = e1 in e2`
  - Multiple parameters: `let x y z ... = e1 in e2`
  - With type annotations: `let (x:U1) y ^U3'(z: U3) ... : U ... = e1 in e2`
- Recursion:
  - Simple: `let rec f x = e1 in e2`
  - With type annotations: `let rec f (x: U1) (^U2) :U3 ^U4  = e1 in e2`
- If-then-else expression: `if e1 then e2 else e3`
- Sequence of expressions: `e1; e2`
- Type ascription: `(e : U)`
- Reset expression: 
    - Simple: `reset e` 
    - with type annotations: `reset^U e`
- Shift expression:
    - Simple: `shift k -> e`
    - with type annotations: `shift (k:U) -> e`
- Pure expression: `pure e`

### Types `U`
- Dynamic type: `?`
- Base types: `bool`, `int`, and `unit`
- Function type: `U -> U`
- Type variables: `'a`, `'b`, ...

### Comments
- Simple: `(* comments *)`
- Nested comments: `(* leave comments here (* nested comments are also supported *) *)`


## Contents
- `bin`: Entry point of the interpreter
- `lib`: Implementation of the calculus
- `test`: Unit tests