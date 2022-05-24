use std::fs;
use std::path::PathBuf;

use super::super::ast;
use super::parse;

fn get_path(rel_p: &str) -> PathBuf {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.push("..");
    p.push(rel_p);
    p
}

fn get_ast(rel_p: &str) -> ast::Module {
    let path = get_path(rel_p);
    let s = fs::read_to_string(path).expect("read file fail");
    parse(&s)
}

#[test]
fn advisor() {
    let _t = get_ast("example/accept/advisor.mag");
}

#[test]
fn matrix() {
    let _t = get_ast("example/accept/mat.mag");
}

#[test]
fn qsort() {
    let _t = get_ast("example/accept/qs.mag");
}
