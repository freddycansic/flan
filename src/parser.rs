use crate::lexer::{Literal, PrimitiveType, Token, TokenType, TokenValue};
use anyhow::{Context, Result, anyhow, bail};
use std::iter::Peekable;
use std::vec::IntoIter;

#[derive(Debug, PartialEq)]
pub struct Program {
    pub functions: Vec<Function>,
}

#[derive(Debug, PartialEq)]
pub struct Function {
    name: String,
    return_type: PrimitiveType,
    statements: Vec<Statement>,
    returns: Option<Expression>,
}

/// ```
/// x = 2;
/// int64 x = 2;
/// print("hello");
/// ```
#[derive(Debug, PartialEq)]
pub enum Statement {
    Assignment(Assignment),
    Declaration(Declaration),
    FunctionCall(FunctionCall),
}

#[derive(Debug, PartialEq)]
pub struct Assignment {
    variable: String,
    expression: Expression,
}

#[derive(Debug, PartialEq)]
pub struct Declaration {
    ty: PrimitiveType,
    variable: String,
    expression: Expression,
}

#[derive(Debug, PartialEq)]
pub struct FunctionCall {
    name: String,
    arguments: Vec<Expression>,
}

/// ```
/// 1
/// 1 + 2
/// 1 + 2 + 3
/// print(3)
/// square(5) + 1
/// ```
#[derive(Debug, PartialEq)]
pub enum Expression {
    Literal(Literal),
}

pub struct Parser {
    iterator: Peekable<IntoIter<Token>>,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self {
            iterator: tokens.into_iter().peekable(),
        }
    }

    fn expect_token_type(&mut self, expected_type: TokenType) -> Result<TokenValue> {
        let token = self
            .iterator
            .next()
            .with_context(|| format!("No more tokens to consume, expected {:?}", expected_type))?;

        if token.ty != expected_type {
            bail!("Unexpected token {:?}, expected {:?}", token, expected_type);
        }

        Ok(token.value)
    }

    fn expect_identifier(&mut self) -> Result<String> {
        if let TokenValue::Identifier(identifier) = self.expect_token_type(TokenType::Identifier)? {
            Ok(identifier)
        } else {
            panic!(
                "This should never happen because if expect_token_type returns an error it gets propagated to expect_identifier"
            )
        }
    }

    fn expect_type(&mut self) -> Result<PrimitiveType> {
        if let TokenValue::PrimitiveType(primitive_type) =
            self.expect_token_type(TokenType::PrimitiveType)?
        {
            Ok(primitive_type)
        } else {
            panic!(
                "This should never happen because if expect_token_type returns an error it gets propagated to expect_type"
            )
        }
    }

    fn expect_literal(&mut self) -> Result<Literal> {
        if let TokenValue::Literal(literal) = self.expect_token_type(TokenType::Literal)? {
            Ok(literal)
        } else {
            panic!(
                "This should never happen because if expect_token_type returns an error it gets propagated to expect_literal"
            )
        }
    }

    fn parse_expression(&mut self) -> Result<Expression> {
        // TODO: implement expression parsing
        let literal = self.expect_literal()?;

        Ok(Expression::Literal(literal))
    }

    fn parse_statement(&mut self) -> Result<Statement> {
        // Statement is a declaration
        if let Some(next_token) = self.iterator.peek()
            && next_token.ty == TokenType::PrimitiveType
        {
            let ty = self.expect_type()?;
            let variable = self.expect_identifier()?;
            self.expect_token_type(TokenType::Assign)?;
            let expression = self.parse_expression()?;
            self.expect_token_type(TokenType::Semicolon)?;

            Ok(Statement::Declaration(Declaration {
                ty,
                variable,
                expression,
            }))
        } else if let Ok(identifier) = self.expect_identifier() {
            // Statement is a function call
            if let Some(next_token) = self.iterator.peek()
                && next_token.ty == TokenType::OpenRoundBracket
            {
                self.expect_token_type(TokenType::OpenRoundBracket)?;
                // TODO: parse arguments
                self.expect_token_type(TokenType::CloseRoundBracket)?;
                self.expect_token_type(TokenType::Semicolon)?;

                Ok(Statement::FunctionCall(FunctionCall {
                    name: identifier,
                    arguments: vec![],
                }))
            // Statement is an assignment
            } else {
                self.expect_token_type(TokenType::Assign)?;
                let expression = self.parse_expression()?;
                self.expect_token_type(TokenType::Semicolon)?;

                Ok(Statement::Assignment(Assignment {
                    variable: identifier,
                    expression,
                }))
            }
        } else {
            Err(anyhow!("Could not parse statement."))
        }
    }

    fn parse_function(&mut self) -> Result<Function> {
        self.expect_token_type(TokenType::Def)?;
        let name = self.expect_identifier()?;
        self.expect_token_type(TokenType::OpenRoundBracket)?;
        // TODO parameters
        self.expect_token_type(TokenType::CloseRoundBracket)?;
        self.expect_token_type(TokenType::Returns)?;
        let return_type = self.expect_type()?;
        self.expect_token_type(TokenType::OpenCurlyBracket)?;

        let mut statements = vec![];
        loop {
            let current_iterator = self.iterator.clone();

            match self.parse_statement() {
                Ok(statement) => statements.push(statement),
                Err(_) => {
                    self.iterator = current_iterator;
                    break;
                }
            }
        }

        let return_expression = if return_type != PrimitiveType::Void {
            // TODO expect expression for return
            Some(self.parse_expression()?)
        } else {
            None
        };

        self.expect_token_type(TokenType::CloseCurlyBracket)?;

        Ok(Function {
            name,
            return_type,
            statements,
            returns: return_expression,
        })
    }

    pub fn parse(&mut self) -> Result<Program> {
        let mut program = Program {
            functions: Vec::new(),
        };

        while let Some(token) = self.iterator.peek() {
            if token.ty == TokenType::Def {
                program.functions.push(self.parse_function()?);
            }
        }

        Ok(program)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;

    #[test]
    fn test_parse_statement_declaration() {
        let mut parser = Parser::new(Lexer::new("int64 a = 3;").lex().unwrap());
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::Declaration(Declaration {
                ty: PrimitiveType::Int64,
                variable: "a".to_owned(),
                expression: Expression::Literal(Literal::Int64(3))
            })
        );

        let mut parser = Parser::new(Lexer::new("int64 a = 3").lex().unwrap());
        assert!(parser.parse_statement().is_err());

        let mut parser = Parser::new(Lexer::new("int64 a 3;").lex().unwrap());
        assert!(parser.parse_statement().is_err());
    }

    #[test]
    fn test_parse_statement_assign() {
        let mut parser = Parser::new(Lexer::new("a = 3;").lex().unwrap());
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::Assignment(Assignment {
                variable: "a".to_owned(),
                expression: Expression::Literal(Literal::Int64(3))
            })
        );

        let mut parser = Parser::new(Lexer::new("a = 3").lex().unwrap());
        assert!(parser.parse_statement().is_err());

        let mut parser = Parser::new(Lexer::new("a 3;").lex().unwrap());
        assert!(parser.parse_statement().is_err());
    }

    #[test]
    fn test_parse_statement_function_call() {
        let mut parser = Parser::new(Lexer::new("print(\"hello, world!\");").lex().unwrap());
        assert_eq!(
            parser.parse_statement().unwrap(),
            Statement::FunctionCall(FunctionCall {
                name: "print".to_owned(),
                arguments: vec![Expression::Literal(Literal::String(
                    "hello, world!".to_owned()
                ))]
            })
        );
    }

    #[test]
    fn test_parse_function() {
        let mut parser = Parser::new(Lexer::new("def main() => void {}").lex().unwrap());
        assert_eq!(
            parser.parse_function().unwrap(),
            Function {
                name: "main".to_owned(),
                return_type: PrimitiveType::Void,
                statements: Vec::new(),
                returns: None,
            }
        );

        let mut parser = Parser::new(Lexer::new("def three() => int64 { 3 }").lex().unwrap());
        assert_eq!(
            parser.parse_function().unwrap(),
            Function {
                name: "three".to_owned(),
                return_type: PrimitiveType::Int64,
                statements: Vec::new(),
                returns: Some(Expression::Literal(Literal::Int64(3))),
            }
        );

        let mut parser = Parser::new(
            Lexer::new("def test() => int64 { int64 a = 3; float64 b = 3.0; 5 }")
                .lex()
                .unwrap(),
        );
        assert_eq!(
            parser.parse_function().unwrap(),
            Function {
                name: "test".to_owned(),
                return_type: PrimitiveType::Int64,
                statements: vec![
                    Statement::Declaration(Declaration {
                        ty: PrimitiveType::Int64,
                        variable: "a".to_owned(),
                        expression: Expression::Literal(Literal::Int64(3))
                    }),
                    Statement::Declaration(Declaration {
                        ty: PrimitiveType::Float64,
                        variable: "b".to_owned(),
                        expression: Expression::Literal(Literal::Float64(3.0))
                    })
                ],
                returns: Some(Expression::Literal(Literal::Int64(5))),
            }
        );
    }
}
