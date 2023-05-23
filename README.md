# The Shark compiler

**This is a compiler for custom designed Shark language - a compiled language based on the Cranelift
backend.**

## Compiler Design

The source files are compiled through essentially 3 layers of Intermediate Representations (IR).

The first layer of IR being the AST, which is parsed in the same pass as tokenizing. The AST is a
free-formed tree structure and is a directly representation to the syntax of the source file, every
node is attached with a `SourceLocation` that indicates the span of the node in the source file.

After the AST is parsed in the first pass, a `GlobalContext` will be generated by visiting every
root node of the AST, the `GlobalContext` stores all global symbols (typedefs, static datas,
functions). After that, the second layer of IR - the Mid-Level IR will be generated. Function bodies
in MIR are flattened to Basic Blocks, similar to CFG in SSA formed IR's. But unlike SSA formed IR's,
variables in function bodies of MIR can be mutable, and variable declarations are stored alongside
the body, instead of having variable declaration statements scattered around functions. The overall
design of MIR is very similar to Rust's MIR, except aggregated values aren't expanded yet, as Shark
doesn't have a borrow checker so it is not deemed to be necessary (by me), for the same reason, the.
MIR is also not attached with source location information. Additionally, like Rust's MIR, functions
in Shark MIR has a promoted values section, which contains local values that need to be promoted
into the static memory. The syntax and type check is also performed in the same pass as the MIR
conversion.

Finally after the MIR is generated, the final pass (the 3.5th pass?) will be the codegen pass, which
will convert the MIR into Cranelift IR.

## TODOs until it is feature-equivalent to C:

(AST) / (MIR) means which stage of work this feature is in.

- [ ] Referencing and dereferencing (MIR)
- [ ] Loop (AST)
- [ ] Math Operators (AST)
- [ ] Partial type infer (needed for number literals, AST)
- [ ] External functions (AST)
- [ ] Static datas (AST)
- [ ] Static promotions (AST)
- [ ] Structs (AST)
- [ ] Unions (AST)
- [ ] Enums (AST)

## Trying on the current compiler:

The current compilers does some very basic things, such as variables and functions, type
expressions, tuples, type infer (but no partial type infer), and mutability.

The current compiler can be used by cloning this repository and running:

```bash
# build the compiler
$ cargo build --release

# compile a source file into object file `output.o`
# note that the compiler will output a lot of debug information,
# as it is not currently intended for any use outside of debug anyways
$ ./target/release/sharkc source.shark

# link and run the object file
$ clang output.o
$ ./a.out
```

Here is a simple shark source file that demostrates some of the current features:

```rust
fn id(x: i32) -> i32 {
    return x;
}

fn main() -> i32 {
    let mut x: (i32, bool);
    // all integer literals are `i32` for now, as partial type infer hasn't been added yet.
    x._0 = id(255);
    x._1 = false;
    if !x._1 {
        return x._0;
    } else {
        return 0;
    }
}
```

Running this program will yield error code `255` in the shell.
