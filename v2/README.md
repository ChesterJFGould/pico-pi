# A Tiny Dependent Language

Type checker and normalizer are in `core.rkt`, frontend is in `pico-pi.rkt`.
Take a look at `examples/ind-nat.pp` for an encoding of natural numbers with an
induction principle in the current language.

# Plan of Action

## Core Language
1. [x] Core language
2. [x] W-Types
3. [x] Natural number encoding and proofs
4. [ ] First class data type descriptions
5. [ ] Bidirectional implicit parameters

## Hello, World!
1. [ ] Quantitative Type Theory
2. [ ] IO Monad
3. [ ] Interpreter for IO Monad
4. [ ] Hello, World!

## Misc. Fun
+ [ ] Improved Syntax
+ [ ] Rewrite Type Checker
	- Fix `VChoice` equality checking (see giant TODO in `value=?`)

## Directed Study
+ [ ] Pull out as library with Racket embedding

## Self Hosting
+ [ ] S-expr datatype and parsing
+ [ ] S-expr syntax?
+ [ ] Type checker
+ [ ] Well typed meta-circular embedding
+ [ ] Compiler
+ [ ] Type preserving compiler for JIT fun

## World Domination
+ [ ] Music DSL
+ [ ] Assembly DSL
+ [ ] OS in assembly DSL
+ [ ] Survey DSL
+ [ ] Nanopass DSL
