# C Compiler

A fully-featured compiler front-end and back-end written in C, implementing all major phases of compilation — from lexical analysis through optimization and target code generation.

## Overview

This project implements a **multi-phase compiler** for a simple imperative language supporting `int`, `float`, and `bool` types, arithmetic/logical expressions, control flow (`if`/`else`, `while`), and `print` statements.

## Compiler Phases

| Phase | Description |
|-------|-------------|
| **1 — Lexical Analysis** | Tokenizes source code into a stream of typed tokens (keywords, identifiers, literals, operators, delimiters). |
| **2 — Syntax Analysis (LL(1))** | Constructs FIRST/FOLLOW sets, builds an LL(1) parsing table, and performs top-down predictive parsing with full stack traces. |
| **3 — Syntax Analysis (Shift-Reduce)** | Implements a bottom-up shift-reduce parser for validation alongside the LL(1) parser. |
| **4 — Parse Tree Construction** | Builds a recursive-descent parse tree (AST) with error recovery and synchronization. |
| **5 — Symbol Table & Semantic Analysis** | Manages scoped symbol tables with type checking, undeclared/redeclared variable detection, and type compatibility validation. |
| **6 — Derivations** | Generates leftmost and rightmost derivation sequences for each parsed statement. |
| **7 — Intermediate Code Generation (TAC)** | Translates the AST into Three-Address Code (quadruples) with temporary variables, labels, and scope-aware name mangling. Includes a step-by-step translation viewer. |
| **8 — Optimization & Target Code** | Applies iterative optimization passes (constant folding, copy propagation, dead code elimination) and generates pseudo-assembly target code. |

## Language Features

- **Types:** `int`, `float`, `bool`
- **Operators:** `+`, `-`, `*`, `/`, `%`, `&&`, `||`, `!`, relational (`<`, `>`, `<=`, `>=`, `==`, `!=`)
- **Control Flow:** `if` / `else`, `while` loops
- **I/O:** `print()` statement
- **Scoping:** Block-scoped variables with nested scope support

## Building & Running

### Compile

```bash
gcc -o week7.exe week7.c
```

### Run

```bash
./week7.exe input.txt
```

The compiler reads the source file specified as a command-line argument and runs all phases sequentially, printing detailed output for each phase.

### Example Input (`input.txt`)

```c
int a;
int b;
int sum;
float avg;
a = 2 * (3 + 4);
b = 15;
sum = 0;
while (a < b && b != 0) {
    int temp;
    temp = a * 2;
    if ((temp % 3 == 0) || (a > 5)) {
        sum = sum + temp;
    } else {
        sum = sum - 1;
    }
    a = a + 1;
}
avg = sum / (b - a);
if (!(avg < 5.0)) {
    print(sum);
} else {
    print(avg);
}
```

## Project Structure

```
├── week7.c          # Complete compiler source code (all phases)
├── input.txt        # Sample input program
├── .gitignore       # Git ignore rules
└── README.md        # This file
```

## Output

When run, the compiler produces:

- **Token listing** from lexical analysis
- **Grammar productions**, FIRST/FOLLOW sets, and LL(1) parsing table
- **Parse traces** for both LL(1) and Shift-Reduce parsers
- **Parse tree** visualization
- **Symbol table** with scope and type information
- **Semantic analysis** error reports (if any)
- **Three-Address Code** (quadruples) for the full program
- **Optimized TAC** after constant folding, copy propagation, and dead code elimination
- **Pseudo-assembly** target code
- **Interactive step-by-step viewer** for individual statement translation
