use anyhow::{Context, Result, bail};
use itertools::Itertools;
use std::iter::{Enumerate, Peekable};
use std::str::Chars;

#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    pub ty: TokenType,
    pub value: TokenValue,
}

impl Token {
    fn just(ty: TokenType) -> Self {
        Token {
            ty,
            value: TokenValue::None,
        }
    }

    fn primitive(primitive_type: PrimitiveType) -> Self {
        Token {
            ty: TokenType::PrimitiveType,
            value: TokenValue::PrimitiveType(primitive_type),
        }
    }

    fn identifier<S: Into<String>>(identifier: S) -> Self {
        Token {
            ty: TokenType::Identifier,
            value: TokenValue::Identifier(identifier.into()),
        }
    }

    fn literal(literal: Literal) -> Self {
        Token {
            ty: TokenType::Literal,
            value: TokenValue::Literal(literal),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TokenValue {
    None,
    Identifier(String),
    PrimitiveType(PrimitiveType),
    Literal(Literal),
}

#[derive(PartialEq, Debug, Clone)]
pub enum TokenType {
    // Keywords
    Def,

    Identifier,
    PrimitiveType,
    // TODO custom type
    Literal,

    // Operator
    Equals,
    Assign,
    Returns,
    Plus,
    Minus,
    Times,
    Divide,

    // Punctuation
    Semicolon,
    OpenCurlyBracket,
    CloseCurlyBracket,
    OpenRoundBracket,
    CloseRoundBracket,
    OpenSquareBracket,
    CloseSquareBracket,
}

#[derive(PartialEq, Debug, Clone)]
pub enum PrimitiveType {
    Int64,
    Float64,
    Void,
}

#[derive(PartialEq, Debug, Clone)]
pub enum Literal {
    Int64(i64),
    Float64(f64),
    String(String),
    Bool(bool),
}

fn characterise_string_token(string: String) -> Token {
    match string.as_str() {
        "def" => Token::just(TokenType::Def),
        "int64" => Token::primitive(PrimitiveType::Int64),
        "float64" => Token::primitive(PrimitiveType::Float64),
        "void" => Token::primitive(PrimitiveType::Void),
        _ => Token::identifier(string),
    }
}

fn characterise_equals_operator(iterator: &mut Peekable<Enumerate<Chars>>) -> Token {
    match iterator.peek() {
        Some((_, '=')) => {
            iterator.next();
            Token::just(TokenType::Equals)
        }
        Some((_, '>')) => {
            iterator.next();
            Token::just(TokenType::Returns)
        }
        _ => Token::just(TokenType::Assign),
    }
}

pub struct Lexer<'a> {
    source: String,
    iterator: Peekable<Enumerate<Chars<'a>>>,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str) -> Self {
        let iterator = source.chars().enumerate().peekable();
        Lexer {
            source: source.to_owned(),
            iterator,
        }
    }

    pub fn get_characters_until<F>(&mut self, start_index: usize, until_true: F) -> String
    where
        F: Fn((usize, char)) -> bool,
    {
        let mut start_of_string = self.iterator.clone();

        let num_characters = start_of_string
            .position(until_true)
            .unwrap_or(self.source.len() - start_index - 1);

        self.iterator.advance_by(num_characters).unwrap();

        self.source[start_index..=start_index + num_characters].to_owned()
    }

    pub fn lex(&mut self) -> Result<Vec<Token>> {
        let mut tokens = Vec::new();

        while let Some((i, character)) = self.iterator.next() {
            if character.is_whitespace() {
                continue;
            }

            // We're reading a string, could be a keyword, identifier, etc
            if character.is_ascii_alphabetic() {
                let string_characters = self.get_characters_until(i, |(_, string_character)| {
                    !string_character.is_ascii_alphanumeric()
                });

                tokens.push(characterise_string_token(string_characters));

                continue;
            }

            if character == '\"' {
                let literal_characters = self
                    .get_characters_until(i, |(_, literal_character)| literal_character == '\"');

                // TODO escaped characters

                tokens.push(Token::literal(Literal::String(
                    // TODO excludes first double quote as get_characters_until includes first character
                    literal_characters[1..literal_characters.len()].to_owned(),
                )));
                continue;
            }

            if character.is_numeric() {
                let number_string = self.get_characters_until(i, |(_, numeric_character)| {
                    !numeric_character.is_numeric() && numeric_character != '.'
                });

                let num_points = number_string.chars().positions(|char| char == '.').count();

                if num_points > 1
                    || number_string.chars().next().unwrap() == '.'
                    || number_string.chars().last().unwrap() == '.'
                {
                    bail!(
                        "Misplaced decimal points in numeric string \"{}\"",
                        number_string
                    );
                }

                if num_points == 1 {
                    tokens.push(Token::literal(Literal::Float64(
                        number_string.parse::<f64>().with_context(|| {
                            format!("Cannot parse floating point value \"{}\"", number_string)
                        })?,
                    )));
                } else {
                    tokens.push(Token::literal(Literal::Int64(
                        number_string.parse::<i64>().with_context(|| {
                            format!("Cannot parse integer value \"{}\"", number_string)
                        })?,
                    )));
                }

                continue;
            }

            let token = match character {
                '{' => Token::just(TokenType::OpenCurlyBracket),
                '}' => Token::just(TokenType::CloseCurlyBracket),
                '(' => Token::just(TokenType::OpenRoundBracket),
                ')' => Token::just(TokenType::CloseRoundBracket),
                '[' => Token::just(TokenType::OpenSquareBracket),
                ']' => Token::just(TokenType::CloseSquareBracket),
                ';' => Token::just(TokenType::Semicolon),
                '+' => Token::just(TokenType::Plus),
                '-' => Token::just(TokenType::Minus),
                '*' => Token::just(TokenType::Times),
                '/' => Token::just(TokenType::Divide),
                '=' => characterise_equals_operator(&mut self.iterator),
                _ => bail!("Unrecognised token \"{}\"", character),
            };

            tokens.push(token);
        }

        Ok(tokens)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MINIMAL_PROGRAM: &str = "def main() => void {
}";

    const LARGER_PROGRAM: &str = "def main() => void {
    int64 a = square(3) ;
    int64 b = square(4);

    int64 c = a + b;

    print(c);
}

def square(int64 a) {
    a * a
}";

    #[test]
    fn test_lex() {
        assert_eq!(
            Lexer::new(MINIMAL_PROGRAM).lex().unwrap(),
            vec![
                Token::just(TokenType::Def),
                Token::identifier("main"),
                Token::just(TokenType::OpenRoundBracket),
                Token::just(TokenType::CloseRoundBracket),
                Token::just(TokenType::Returns),
                Token::primitive(PrimitiveType::Void),
                Token::just(TokenType::OpenCurlyBracket),
                Token::just(TokenType::CloseCurlyBracket)
            ]
        );

        assert_eq!(
            Lexer::new(LARGER_PROGRAM).lex().unwrap(),
            vec![
                // def main() => void {
                Token::just(TokenType::Def),
                Token::identifier("main"),
                Token::just(TokenType::OpenRoundBracket),
                Token::just(TokenType::CloseRoundBracket),
                Token::just(TokenType::Returns),
                Token::primitive(PrimitiveType::Void),
                Token::just(TokenType::OpenCurlyBracket),
                // int64 a = square(3);
                Token::primitive(PrimitiveType::Int64),
                Token::identifier("a"),
                Token::just(TokenType::Assign),
                Token::identifier("square"),
                Token::just(TokenType::OpenRoundBracket),
                Token::literal(Literal::Int64(3)),
                Token::just(TokenType::CloseRoundBracket),
                Token::just(TokenType::Semicolon),
                // int64 b = square(4);
                Token::primitive(PrimitiveType::Int64),
                Token::identifier("b"),
                Token::just(TokenType::Assign),
                Token::identifier("square"),
                Token::just(TokenType::OpenRoundBracket),
                Token::literal(Literal::Int64(4)),
                Token::just(TokenType::CloseRoundBracket),
                Token::just(TokenType::Semicolon),
                // int64 c = a + b;
                Token::primitive(PrimitiveType::Int64),
                Token::identifier("c"),
                Token::just(TokenType::Assign),
                Token::identifier("a"),
                Token::just(TokenType::Plus),
                Token::identifier("b"),
                Token::just(TokenType::Semicolon),
                // print(c);
                Token::identifier("print"),
                Token::just(TokenType::OpenRoundBracket),
                Token::identifier("c"),
                Token::just(TokenType::CloseRoundBracket),
                Token::just(TokenType::Semicolon),
                Token::just(TokenType::CloseCurlyBracket),
                // def square(int64 a) { a * a }
                Token::just(TokenType::Def),
                Token::identifier("square"),
                Token::just(TokenType::OpenRoundBracket),
                Token::primitive(PrimitiveType::Int64),
                Token::identifier("a"),
                Token::just(TokenType::CloseRoundBracket),
                Token::just(TokenType::OpenCurlyBracket),
                Token::identifier("a"),
                Token::just(TokenType::Times),
                Token::identifier("a"),
                Token::just(TokenType::CloseCurlyBracket),
            ]
        );
    }
}
