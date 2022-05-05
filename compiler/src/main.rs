use calocom_compiler::compile_with_arguments;
use calocom_compiler::Args;
use clap::Parser;

fn main() {
    compile_with_arguments(Args::parse()).unwrap_or(());
}
