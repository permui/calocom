extern crate pest;

#[macro_use]
extern crate pest_derive;

pub mod ast;
pub mod backend;
pub mod frontend;
pub mod midend;
pub mod sym;

use backend::codegen::*;
use clap::{ArgEnum, Parser};
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine,
};
use inkwell::OptimizationLevel;
use midend::middle_ir::MiddleIR;
use midend::typed_ast::TypedAST;
use owo_colors::OwoColorize;
use std::collections::HashSet;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use inkwell::context::Context;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
pub struct Args {
    /// Specify the runtime file
    #[clap(long, default_value = "calocom_runtime.ll", parse(from_os_str))]
    runtime: PathBuf,

    /// Specify the optimizing level
    #[clap(short, long, arg_enum, default_value_t = OptLevel::O3)]
    level: OptLevel,

    /// Specify the type of the output file
    #[clap(short, long, arg_enum)]
    r#type: Vec<OutputType>,

    /// Specify the input file
    #[clap(parse(from_os_str))]
    file: PathBuf,

    /// Specify the output file
    #[clap(short, long, parse(from_os_str))]
    output: Option<PathBuf>,

    /// Specify the relocation type
    #[clap(short, long, arg_enum, default_value_t = Relocate::Pic)]
    relocate: Relocate,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, ArgEnum)]
#[clap(rename_all = "verbatim")]
enum OptLevel {
    O0,
    O1,
    O2,
    O3,
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, ArgEnum)]
enum OutputType {
    #[clap(name = "llvm-bc")]
    LLVMBitcode,
    #[clap(name = "llvm-asm")]
    LLVMAsm,
    #[clap(name = "mir")]
    MiddleIR,
    #[clap(name = "tast")]
    TypedAST,
    Asm,
    Bin,
    Obj,
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, ArgEnum)]
enum Relocate {
    Static,
    DynamicNoPic,
    Pic,
    Default,
}

fn check_flag_and_do<F>(flags: &mut HashSet<OutputType>, flag: OutputType, f: F) -> Result<(), ()>
where
    F: FnOnce(),
{
    if flags.contains(&flag) {
        f();
    }
    flags.remove(&flag);
    if flags.is_empty() {
        Err(())
    } else {
        Ok(())
    }
}

fn call_system_linker(input: &Path, output: &Path) -> Result<Output, String> {
    if cfg!(target_os = "linux") {
        Command::new("cc")
            .args([input.as_os_str(), OsStr::new("-o"), output.as_os_str()])
            .output()
            .map_err(|e| e.to_string())
    } else {
        Err("Target os not supported".to_string())
    }
}

pub fn compile_with_arguments(args: Args) -> Result<(), ()> {
    let input_file = args.file.canonicalize().unwrap();
    if input_file.is_dir() {
        panic!("{} is a directory", input_file.display());
    }

    let output_type = args.r#type;
    let mut output_file = args.output.as_ref().unwrap_or(&input_file).clone();
    let mut output_kinds: HashSet<_> = output_type.into_iter().collect();

    if output_file.is_dir() {
        output_file = output_file.with_file_name(
            input_file
                .as_path()
                .file_name()
                .expect("Do not use .. as input file name"),
        );
    }

    let source = fs::read_to_string(&input_file).expect("Read file failed");
    let ast = frontend::parse(&source);
    let ty_ast: TypedAST = ast.into();

    check_flag_and_do(&mut output_kinds, OutputType::TypedAST, || {
        let output_file = output_file.with_extension("tast.ir");
        fs::write(&output_file, format!("{:#?}", ty_ast)).expect("Write TypedAST failed");
        println!(
            "{} Write typed ast into {:?}",
            "::".green(),
            output_file.as_os_str().blue()
        )
    })?;

    let mir: MiddleIR = ty_ast.into();

    check_flag_and_do(&mut output_kinds, OutputType::MiddleIR, || {
        let output_file = output_file.with_extension("mir.ir");
        fs::write(&output_file, format!("{:#?}", mir)).expect("Write Middle IR failed");
        println!(
            "{} Write middle IR into {:?}",
            "::".green(),
            output_file.as_os_str().blue()
        )
    })?;

    let ctx = Context::create();
    let module_name = input_file.as_os_str().to_string_lossy();
    let mut codegen = CodeGen::new(module_name.as_ref(), &ctx, &mir, args.runtime.as_path());
    codegen.emit_all(&mir);

    check_flag_and_do(&mut output_kinds, OutputType::LLVMBitcode, || {
        let output_file = output_file.with_extension("bc");
        codegen.module.write_bitcode_to_path(&output_file);
        println!(
            "{} Write llvm bitcode into {:?}",
            "::".green(),
            output_file.as_os_str().blue()
        )
    })?;

    check_flag_and_do(&mut output_kinds, OutputType::LLVMAsm, || {
        let output_file = output_file.with_extension("ll");
        codegen.module.print_to_file(&output_file).unwrap();
        println!(
            "{} Write llvm assembly into {:?}",
            "::".green(),
            output_file.as_os_str().blue()
        )
    })?;

    Target::initialize_native(&InitializationConfig::default())
        .expect("Failed to initialize native target");

    let triple = TargetMachine::get_default_triple();
    let cpu = TargetMachine::get_host_cpu_name().to_string();
    let features = TargetMachine::get_host_cpu_features().to_string();

    let opt = match args.level {
        OptLevel::O0 => OptimizationLevel::None,
        OptLevel::O1 => OptimizationLevel::Less,
        OptLevel::O2 => OptimizationLevel::Default,
        OptLevel::O3 => OptimizationLevel::Aggressive,
    };
    let reloc = match args.relocate {
        Relocate::Static => RelocMode::Static,
        Relocate::DynamicNoPic => RelocMode::DynamicNoPic,
        Relocate::Pic => RelocMode::PIC,
        Relocate::Default => RelocMode::Default,
    };
    let target = Target::from_triple(&triple).unwrap();
    let target_machine = target
        .create_target_machine(&triple, &cpu, &features, opt, reloc, CodeModel::Default)
        .unwrap();

    check_flag_and_do(&mut output_kinds, OutputType::Asm, || {
        let output_file = output_file.with_extension("s");
        target_machine
            .write_to_file(&codegen.module, FileType::Assembly, &output_file)
            .unwrap();
        println!(
            "{} Write native assembly into {:?}",
            "::".green(),
            output_file.as_os_str().blue()
        )
    })?;

    let mut has_object = false;
    check_flag_and_do(&mut output_kinds, OutputType::Obj, || {
        let output_file = output_file.with_extension("o");
        target_machine
            .write_to_file(&codegen.module, FileType::Object, &output_file)
            .unwrap();
        println!(
            "{} Write object file into {:?}",
            "::".green(),
            output_file.as_os_str().blue()
        );
        has_object = true;
    })?;

    check_flag_and_do(&mut output_kinds, OutputType::Bin, || {
        let output_file = output_file.with_extension("o");
        if !has_object {
            target_machine
                .write_to_file(&codegen.module, FileType::Object, &output_file)
                .unwrap();
            println!(
                "{} Write object file into {:?}",
                "::".green(),
                output_file.as_os_str().blue()
            );
        }
        let object_file = output_file.with_extension("o");
        let output_file = if cfg!(target_os = "windows") {
            output_file.with_extension("exe")
        } else {
            output_file.with_extension("")
        };
        if !object_file.exists() {
            panic!("Object file not found")
        }
        let handle_err = |err: String| -> Result<(), ()> {
            println!("{} {:?}", "::".red(), err.as_str());
            Err(())
        };
        let handle_output = |out: Output| -> Result<(), ()> {
            if out.status.success() {
                println!("{} Try to link the object file", "::".green());
            } else {
                println!("{} Try to link the object file", "::".red());
            }
            let stdout = std::str::from_utf8(out.stderr.as_slice()).unwrap_or_default();
            let stderr = std::str::from_utf8(out.stderr.as_slice()).unwrap_or_default();
            if !stderr.is_empty() || !stdout.is_empty() {
                println!("{} {} {}", "::".red(), stderr, stdout);
                return Err(());
            }
            Ok(())
        };
        if call_system_linker(object_file.as_path(), output_file.as_path())
            .map_or_else(handle_err, handle_output)
            .is_ok()
        {
            println!(
                "{} Write binary file into {:?}",
                "::".green(),
                output_file.as_os_str().blue()
            );
        }
    })?;

    Ok(())
}
