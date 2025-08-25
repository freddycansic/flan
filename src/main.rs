#![feature(iter_advance_by)]

mod lexer;
mod parser;

use itertools::Itertools;
use std::fs;

use crate::lexer::Lexer;
use crate::parser::Parser;

fn main() {
    let source_file = fs::read_to_string("code/draft.fl");
    let tokens = Lexer::new(source_file.unwrap().as_str()).lex().unwrap();
    let ast = Parser::new(tokens).parse().unwrap();

    println!("{:?}", ast.functions.iter().format("\n"));
}
