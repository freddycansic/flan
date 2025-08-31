use crate::lexer::{Literal, Operator, PrimitiveType, Token, TokenType, TokenValue};
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
    BinaryOperation(Box<BinaryOperation>),
    UnaryOperation(Box<UnaryOperation>),
}

#[derive(Debug, PartialEq)]
pub struct BinaryOperation {
    lhs: Expression,
    rhs: Expression,
    operator: Operator,
}

#[derive(Debug, PartialEq)]
pub struct UnaryOperation {
    operand: Expression,
    operator: Operator,
}

type TokenIterator = Peekable<IntoIter<Token>>;

pub struct Parser {
    iterator: TokenIterator,
}

struct Expected<'a, T> {
    iterator: &'a mut TokenIterator,
    value: T,
}

impl<'a, T> Expected<'a, T> {
    fn peek(&self) -> &T {
        &self.value
    }

    fn consume(self) -> T {
        self.iterator.next();
        self.value
    }
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self {
            iterator: tokens.into_iter().peekable(),
        }
    }

    fn expect_token_type(&mut self, expected_type: TokenType) -> Result<Expected<TokenValue>> {
        let token = self
            .iterator
            .peek()
            .with_context(|| format!("No more tokens to consume, expected {:?}", expected_type))?
            .clone();

        if token.ty != expected_type {
            bail!("Unexpected token {:?}, expected {:?}", token, expected_type);
        }

        Ok(Expected {
            iterator: &mut self.iterator,
            value: token.value,
        })
    }

    // TODO this could be a macro...
    fn expect_identifier(&mut self) -> Result<Expected<String>> {
        let Expected { iterator, value } = self.expect_token_type(TokenType::Identifier)?;

        if let TokenValue::Identifier(identifier) = value {
            return Ok(Expected {
                iterator,
                value: identifier,
            });
        }

        panic!("Something very bad has happened")
    }

    fn expect_type(&mut self) -> Result<Expected<PrimitiveType>> {
        let Expected { iterator, value } = self.expect_token_type(TokenType::PrimitiveType)?;

        if let TokenValue::PrimitiveType(primitive_type) = value {
            return Ok(Expected {
                iterator,
                value: primitive_type,
            });
        }

        panic!("Something very bad has happened")
    }

    fn expect_literal(&mut self) -> Result<Expected<Literal>> {
        let Expected { iterator, value } = self.expect_token_type(TokenType::Literal)?;

        if let TokenValue::Literal(literal) = value {
            return Ok(Expected {
                iterator,
                value: literal,
            });
        }

        panic!("Something very bad has happened")
    }

    fn expect_operator(&mut self) -> Result<Expected<Operator>> {
        let Expected { iterator, value } = self.expect_token_type(TokenType::Operator)?;

        if let TokenValue::Operator(operator) = value {
            return Ok(Expected {
                iterator,
                value: operator,
            });
        }

        panic!("Something very bad has happened")
    }

    pub(crate) fn parse_expression(&mut self) -> Result<Expression> {
        self.parse_expression_inner(0)
    }

    fn parse_expression_inner(&mut self, min_binding_power: u32) -> Result<Expression> {
        // TODO allow for unary operators
        // TODO make this not look awful
        // TODO this doesn't invalidate expressions with trailing ) i.e. 1 + 2 + 3) = valid
        let mut lhs = match self.iterator.next() {
            None => bail!("Could not parse expression. No tokens"),
            Some(token) => {
                if token.ty == TokenType::OpenRoundBracket {
                    let lhs = self.parse_expression_inner(0)?;

                    // Holy rust balls
                    (self
                        .iterator
                        .next()
                        .ok_or_else(|| {
                            anyhow!("Could not parse expression. No matching CloseRoundBracket")
                        })?
                        .ty
                        == TokenType::CloseRoundBracket)
                        .ok_or_else(|| {
                            anyhow!("Could not parse expression. No matching CloseRoundBracket")
                        })?;

                    lhs
                } else if let TokenValue::Literal(literal) = token.value {
                    Expression::Literal(literal)
                } else {
                    bail!(
                        "Could not parse expression. Wrong token: {:?}, expected OpenRoundBracket or Literal",
                        token
                    );
                }
            }
        };

        loop {
            let operator = match self.iterator.peek() {
                None => break,
                Some(token) => {
                    if token.ty == TokenType::CloseRoundBracket {
                        break;
                    } else if let TokenValue::Operator(operator) = token.value.clone() {
                        operator
                    } else {
                        bail!(
                            "Could not parse expression. Wrong token: {:?}, expected CloseRoundBracket or Operator",
                            token
                        );
                    }
                }
            };

            let (lhs_binding_power, rhs_binding_power) = operator.binding_power();
            if lhs_binding_power < min_binding_power {
                break;
            }

            self.iterator.next();

            let rhs = self.parse_expression_inner(rhs_binding_power)?;

            lhs = Expression::BinaryOperation(BinaryOperation { lhs, rhs, operator }.into());
        }

        Ok(lhs)
        // let token_type = self
        //     .iterator
        //     .peek()
        //     .with_context(|| "No more tokens, cannot parse expression")?
        //     .ty;

        // match token_type {
        //     TokenType::Literal => self.expect_literal()?,
        //     // TokenType::Identifier => ,
        //     _ => bail!("Unexpected token while parsing expression \"{:?}\"", token_type),
        // }
    }

    fn parse_statement(&mut self) -> Result<Statement> {
        // Statement is a declaration
        if self.expect_type().is_ok() {
            let ty = self.expect_type()?.consume();
            let variable = self.expect_identifier()?.consume();
            self.expect_token_type(TokenType::Assign)?.consume();
            let expression = self.parse_expression()?;
            self.expect_token_type(TokenType::Semicolon)?.consume();

            return Ok(Statement::Declaration(Declaration {
                ty,
                variable,
                expression,
            }));
        }

        let identifier = self.expect_identifier()?.consume();

        // Statement is a function call
        if self.expect_token_type(TokenType::OpenRoundBracket).is_ok() {
            self.expect_token_type(TokenType::OpenRoundBracket)?
                .consume();
            // TODO: parse arguments
            self.expect_token_type(TokenType::CloseRoundBracket)?
                .consume();
            self.expect_token_type(TokenType::Semicolon)?.consume();

            Ok(Statement::FunctionCall(FunctionCall {
                name: identifier,
                arguments: vec![],
            }))
        // Statement is an assignment
        } else {
            self.expect_token_type(TokenType::Assign)?.consume();
            let expression = self.parse_expression()?;
            self.expect_token_type(TokenType::Semicolon)?.consume();

            Ok(Statement::Assignment(Assignment {
                variable: identifier,
                expression,
            }))
        }
    }

    fn parse_function(&mut self) -> Result<Function> {
        self.expect_token_type(TokenType::Def)?.consume();
        let name = self.expect_identifier()?.consume();
        self.expect_token_type(TokenType::OpenRoundBracket)?
            .consume();
        // TODO parameters
        self.expect_token_type(TokenType::CloseRoundBracket)?
            .consume();
        self.expect_token_type(TokenType::Returns)?.consume();
        let return_type = self.expect_type()?.consume();
        self.expect_token_type(TokenType::OpenCurlyBracket)?
            .consume();

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

    // I love ai driven testing
    #[test]
    fn test_parse_expression_single_int() {
        let mut parser = Parser::new(Lexer::new("42").lex().unwrap());
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::Literal(Literal::Int64(42))
        );
    }

    #[test]
    fn test_parse_expression_single_float() {
        let mut parser = Parser::new(Lexer::new("3.14").lex().unwrap());
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::Literal(Literal::Float64(3.14))
        );
    }

    #[test]
    fn test_parse_expression_simple_addition() {
        let mut parser = Parser::new(Lexer::new("1 + 2").lex().unwrap());
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::BinaryOperation(Box::new(BinaryOperation {
                lhs: Expression::Literal(Literal::Int64(1)),
                operator: Operator::Plus,
                rhs: Expression::Literal(Literal::Int64(2)),
            }))
        );
    }

    #[test]
    fn test_parse_expression_precedence() {
        let mut parser = Parser::new(Lexer::new("1 + 2 * 3").lex().unwrap());
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::BinaryOperation(Box::new(BinaryOperation {
                lhs: Expression::Literal(Literal::Int64(1)),
                operator: Operator::Plus,
                rhs: Expression::BinaryOperation(Box::new(BinaryOperation {
                    lhs: Expression::Literal(Literal::Int64(2)),
                    operator: Operator::Times,
                    rhs: Expression::Literal(Literal::Int64(3)),
                })),
            }))
        );
    }

    #[test]
    fn test_parse_expression_with_parentheses() {
        let mut parser = Parser::new(Lexer::new("(1 + 2) * 3").lex().unwrap());
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::BinaryOperation(Box::new(BinaryOperation {
                lhs: Expression::BinaryOperation(Box::new(BinaryOperation {
                    lhs: Expression::Literal(Literal::Int64(1)),
                    operator: Operator::Plus,
                    rhs: Expression::Literal(Literal::Int64(2)),
                })),
                operator: Operator::Times,
                rhs: Expression::Literal(Literal::Int64(3)),
            }))
        );
    }

    #[test]
    fn test_parse_expression_unary_minus_int() {
        let mut parser = Parser::new(Lexer::new("-42").lex().unwrap());
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::UnaryOperation(Box::new(UnaryOperation {
                operator: Operator::Minus,
                operand: Expression::Literal(Literal::Int64(42)),
            }))
        );
    }

    #[test]
    fn test_parse_expression_unary_minus_float() {
        let mut parser = Parser::new(Lexer::new("-3.14").lex().unwrap());
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::UnaryOperation(Box::new(UnaryOperation {
                operator: Operator::Minus,
                operand: Expression::Literal(Literal::Float64(3.14)),
            }))
        );
    }

    #[test]
    fn test_parse_expression_division() {
        let mut parser = Parser::new(Lexer::new("10 / 2").lex().unwrap());
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::BinaryOperation(Box::new(BinaryOperation {
                lhs: Expression::Literal(Literal::Int64(10)),
                operator: Operator::Divide,
                rhs: Expression::Literal(Literal::Int64(2)),
            }))
        );
    }

    #[test]
    fn test_parse_expression_equals() {
        let mut parser = Parser::new(Lexer::new("1 == 1").lex().unwrap());
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::BinaryOperation(Box::new(BinaryOperation {
                lhs: Expression::Literal(Literal::Int64(1)),
                operator: Operator::Equals,
                rhs: Expression::Literal(Literal::Int64(1)),
            }))
        );
    }

    #[test]
    fn test_parse_expression_no_brackets() {
        let mut parser = Parser::new(Lexer::new("1 + 2 * 3 + 4 * 5 + 6").lex().unwrap());
        assert_eq!(
            parser.parse_expression().unwrap(),
            Expression::BinaryOperation(Box::new(BinaryOperation {
                lhs: Expression::BinaryOperation(Box::new(BinaryOperation {
                    lhs: Expression::BinaryOperation(Box::new(BinaryOperation {
                        lhs: Expression::Literal(Literal::Int64(1)),
                        operator: Operator::Plus,
                        rhs: Expression::BinaryOperation(Box::new(BinaryOperation {
                            lhs: Expression::Literal(Literal::Int64(2)),
                            operator: Operator::Times,
                            rhs: Expression::Literal(Literal::Int64(3)),
                        })),
                    })),
                    operator: Operator::Plus,
                    rhs: Expression::BinaryOperation(Box::new(BinaryOperation {
                        lhs: Expression::Literal(Literal::Int64(4)),
                        operator: Operator::Times,
                        rhs: Expression::Literal(Literal::Int64(5)),
                    })),
                })),
                operator: Operator::Plus,
                rhs: Expression::Literal(Literal::Int64(6)),
            }))
        );
    }

    #[test]
    fn test_parse_expression_empty_input() {
        let mut parser = Parser::new(Lexer::new("").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_unexpected_operator() {
        let mut parser = Parser::new(Lexer::new("+").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_missing_operand() {
        let mut parser = Parser::new(Lexer::new("1 +").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_missing_operator() {
        let mut parser = Parser::new(Lexer::new("1 2").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_double_operator() {
        let mut parser = Parser::new(Lexer::new("1 + + 2").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_empty_parentheses() {
        let mut parser = Parser::new(Lexer::new("()").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_operator_in_parentheses() {
        let mut parser = Parser::new(Lexer::new("(+)").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_missing_operand_after_operator() {
        let mut parser = Parser::new(Lexer::new("1 * ").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_missing_operand_before_operator() {
        let mut parser = Parser::new(Lexer::new("* 2").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_invalid_operator_sequence() {
        let mut parser = Parser::new(Lexer::new("1 * / 2").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_operator_at_end() {
        let mut parser = Parser::new(Lexer::new("1 + 2 *").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_operator_at_start() {
        let mut parser = Parser::new(Lexer::new("* 1 + 2").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_missing_operator_in_sequence() {
        let mut parser = Parser::new(Lexer::new("1 2 + 3").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_invalid_token_in_expression() {
        let mut parser = Parser::new(Lexer::new("1 + abc + 2").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_complex_missing_operator() {
        let mut parser = Parser::new(Lexer::new("1 + 2 3 * 4").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_parentheses_without_content() {
        let mut parser = Parser::new(Lexer::new("1 + () + 2").lex().unwrap());
        assert!(parser.parse_expression().is_err());
    }

    #[test]
    fn test_parse_expression_just_operator() {
        let mut parser = Parser::new(Lexer::new("+").lex().unwrap());
        assert!(parser.parse_expression().is_err());
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
