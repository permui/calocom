# Calocom Project

## Build
### Build the runtime
The calocom compiler requires the runtime to be a LLVM IR form so that it can link the runtime before compiling the program into a object file. In a sense, it looks like a typical LTO operation. Because cargo is not intend to let users to modify the compiling options of rustc automatically and easily, we need to build the runtime manually.

To obtain a LLVM IR form of the runtime, we need to run the following command:

```bash
cd runtime
cargo rustc --lib --release -- --emit=llvm-ir
```

Note that it's required to use release mode because we expect to produce a single IR file.

Then found the `calocom_runtime.ll` file in the `target/release/deps` directory.

Usually, the calocom compiler tries to find the runtime file in the current directory with the name `calocom_runtime.ll`. You might modify the default behavior with some flags.

### Build the compiler

The building process goes as normal rust crates.

```bash
cargo build
```

or in release mode:

```bash
cargo build --release
```

## Usage
```text
calocom-compiler 0.1.0

USAGE:
    calocom-compiler [OPTIONS] <FILE>

ARGS:
    <FILE>    Specify the input file

OPTIONS:
    -h, --help                   Print help information
    -l, --opt-level <LEVEL>      Specify the optimizing level [default: O3] [possible values: O0,
                                 O1, O2, O3]
        --llvm-pass-debug        Specify if need to enable debug log for llvm passes
    -o, --output <OUTPUT>        Specify the output file
    -r, --relocate <RELOCATE>    Specify the relocation type [default: pic] [possible values:
                                 static, dynamic-no-pic, pic, default]
        --runtime <RUNTIME>      Specify the runtime file [default: calocom_runtime.ll]
    -t, --type <TYPE>            Specify the type of the output file [possible values: llvm-bc,
                                 llvm-asm, mir, tast, asm, bin, obj]
    -V, --version                Print version information
```