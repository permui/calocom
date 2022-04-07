use std::fs;
use calocom_compiler::frontend;

fn main() {
    let s = fs::read_to_string("./example/stage1/at.mag").expect("read file fail");
    let m = frontend::parse(&s);
    println!("{:#?}", m);
}
