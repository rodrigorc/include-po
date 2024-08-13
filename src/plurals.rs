/// Module to parse and reformat plural expressions
///
/// PO files have the plural expression in a header, written as a single in C-like expression,
/// usually with heavy use of the ternary conditional operator (?:).
///
/// We need to convert that expression into an quivalent Rust expression. This module does two
/// things:
///  * Parse the PO expression.
///  * Format the Rust expression.
///
/// Reference implementation:
/// https://github.com/autotools-mirror/gettext/blob/master/gettext-runtime/intl/plural.y

use nom::{
    *,
    branch::*,
    combinator::*,
    multi::*,
    sequence::*,
    bytes::complete::*,
    character::complete::*,
    error::*,
};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BinOp {
    Add, Sub, Mult, Div, Mod,
    And, Or,
    Eq, Ne, Gt, Ge, Lt, Le,
}

impl BinOp {
    fn get_type(&self) -> Type {
        use BinOp::*;
        use Type::*;
        match self {
            Add | Sub | Mult | Div | Mod => Int,
            And | Or | Eq | Ne | Gt | Ge | Lt | Le => Bool,
        }
    }
    fn arg_type(&self) -> Type {
        use BinOp::*;
        use Type::*;
        match self {
            Add | Sub | Mult | Div | Mod => Int,
            // Do not compare boolean values, that way the non-assciativy of Rust's
            // comparison operators won't be an issue
            Eq | Ne | Gt | Ge | Lt | Le => Int,
            And | Or => Bool,
        }
    }
    // This is the precedence of the output expression, ie, that of Rust
    fn fmt_precedence(&self) -> u32 {
        use BinOp::*;
        match self {
            Or => 1,
            And => 2,
            Eq | Ne | Gt | Ge | Lt | Le => 3,
            Add | Sub => 4,
            Mult | Div | Mod => 5,
            // Unary Not has maximum precedence
        }
    }
}

const PRECEDENCE_NOT: u32 = 6;

/// Other tokens.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Token {
    LParen, RParen,
    Neg,
    Question, Colon,
    N,
}

fn next_token(input: &str) -> IResult<&str, Token> {
    let (input, _) = multispace0(input)?;
    use Token::*;
    let res = alt((
        char('n').map(|_| N),
        char('(').map(|_| LParen),
        char(')').map(|_| RParen),
        char('!').map(|_| Neg),
        char('?').map(|_| Question),
        char(':').map(|_| Colon),
    ))(input)?;
    Ok(res)
}

fn number(input: &str) -> IResult<&str, u32> {
    let (input, _) = multispace0(input)?;
    let (input, n) = u32(input)?;
    Ok((input, n))
}

fn token(tok: Token) -> impl Fn(&str) -> IResult<&str, Token> {
    move |input| {
        let (input, next) = next_token(input)?;
        if tok == next {
            Ok((input, next))
        } else {
            Err(Err::Error(Error::from_error_kind(input, ErrorKind::Tag)))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    N,
    Const(u32),
    // Only one unary op
    Neg(Box<Expr>),
    Binary(Box<Expr>, BinOp, Box<Expr>),
    // Only one ternary op
    Cond(Box<Expr>, Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Type {
    Bool,
    Int,
}

impl Expr {
    pub fn parse(input: &str) -> Result<Expr, Err<Error<&str>>> {
        let (_, expr) = expression(input)?;
        Ok(expr)
    }
    fn new_bin(e1: Expr, op: BinOp, e2: Expr) -> Expr {
        Expr::Binary(Box::new(e1), op, Box::new(e2))
    }
    fn get_type(&self) -> Type {
        use Expr::*;
        use Type::*;
        match self {
            N | Const(_) | Cond(_, _, _) => Int,
            Neg(_) => Bool,
            Binary(_, op, _) => op.get_type(),
        }
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        typed(self, Type::Int, 0).fmt(f)
    }
}

struct TypedExpr<'a> {
    e: &'a Expr,
    ty: Option<Type>,
    precedence: u32
}
fn typed(e: &Expr, ty: Type, precedence: u32) -> TypedExpr<'_> {
    TypedExpr { e, ty: Some(ty), precedence }
}
fn untyped(e: &Expr, precedence: u32) -> TypedExpr<'_> {
    TypedExpr { e, ty: None, precedence }
}

impl std::fmt::Display for TypedExpr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Expr::*;
        use Type::*;
        let TypedExpr{ e, ty, precedence } = *self;
        let paren = |p| if p { ("(",")") } else { ("","") };
        match ty {
            Some(ty) => {
                let my = e.get_type();
                if my == ty {
                    write!(f, "{}", untyped(e, precedence))?;
                } else {
                    match ty {
                        Bool => {
                            // I don't this these parentheses can ever be printed, because of the
                            // trick in Neg/Int, but just in case.
                            let (pl, pr) = paren(precedence > BinOp::Ne.fmt_precedence());
                            write!(f, "{pl}{} != 0{pr}", untyped(e, BinOp::Ne.fmt_precedence()))?;
                        }
                        Int => {
                            write!(f, "u32::from({})", untyped(e, 0))?;
                        }
                    }
                }
            }
            None => {
                match e {
                    N => write!(f, "n")?,
                    Const(x) => write!(f, "{x}")?,
                    Neg(e) => {
                        match e.get_type() {
                            Bool => {
                                // ! has maximum precedence, will never need parentheses
                                write!(f, "!{}", untyped(e, PRECEDENCE_NOT))?;
                            }
                            // Convert '!(a != 0)' to 'a == 0'
                            Int => {
                                let (pl, pr) = paren(precedence > BinOp::Eq.fmt_precedence());
                                write!(f, "{pl}{} == 0{pr}", untyped(e, BinOp::Eq.fmt_precedence()))?;
                            }
                        }
                    }
                    Binary(e1, op, e2) => {
                        let ty = op.arg_type();
                        let prec = op.fmt_precedence();
                        let (pl, pr) = paren(precedence > prec);
                        // increase the required precedence for the rhs, because of the left
                        // associativity.
                        write!(f, "{pl}{} {op} {}{pr}", typed(e1, ty, prec), typed(e2, ty, prec + 1))?;
                    }
                    Cond(e1, e2, e3) => {
                        // Chained if / else / if don't need the second pair of braces.
                        let chained_if = matches!(**e3, Cond(_,_,_));
                        let (bl, br) = if chained_if { ("","") } else { ("{ "," }") };
                        write!(f, "if {} {{ {} }} else {bl}{}{br}",
                            typed(e1, Bool, 0),
                            typed(e2, Int, 0),
                            typed(e3, Int, 0),
                        )?;
                    }
                }
            }
        }
        Ok(())
    }
}

impl Default for Expr {
    /// (n != 1)
    fn default() -> Expr {
        Expr::Binary(Box::new(Expr::N), BinOp::Ne, Box::new(Expr::Const(1)))
    }
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use BinOp::*;
        match self {
            Add => write!(f, "+"),
            Sub => write!(f, "-"),
            Mult => write!(f, "*"),
            Div => write!(f, "/"),
            Mod => write!(f, "%"),
            And => write!(f, "&&"),
            Or => write!(f, "||"),
            Eq => write!(f, "=="),
            Ne => write!(f, "!="),
            Gt => write!(f, ">"),
            Ge => write!(f, ">="),
            Lt => write!(f, "<"),
            Le => write!(f, "<="),
        }
    }
}

pub fn left_assoc<I, O, OP, E: ParseError<I>, F, G, H>(
    mut operator: F,
    mut next: G,
    mut combine: H,
) -> impl FnMut(I) -> IResult<I, O, E>
where
    I: Clone + InputLength,
    F: Parser<I, OP, E>,
    G: Parser<I, O, E>,
    H: FnMut(O, OP, O) -> O,
{
    move |input: I| {
        let (input, expr1) = next.parse(input)?;
        let mut expr1 = Some(expr1);
        let (input, expr) = fold_many0(pair(|i| operator.parse(i), |i| next.parse(i)),
            || expr1.take().unwrap(),
            |e1, (op, e2)| combine(e1, op, e2)
        )(input)?;
        Ok((input, expr))
    }
}

fn bin_op(input: &str) -> IResult<&str, BinOp> {
    let (input, _) = multispace0(input)?;
    use BinOp::*;
    let res = alt((
        tag("&&").map(|_| And),
        tag("||").map(|_| Or),
        tag("==").map(|_| Eq),
        tag("!=").map(|_| Ne),
        tag(">=").map(|_| Ge),
        tag("<=").map(|_| Le),
        char('+').map(|_| Add),
        char('-').map(|_| Sub),
        char('*').map(|_| Mult),
        char('/').map(|_| Div),
        char('%').map(|_| Mod),
        char('>').map(|_| Gt),
        char('<').map(|_| Lt),
    ))(input)?;
    Ok(res)
}

fn bin_op_any(ops: &[BinOp]) -> impl Fn(&str) -> IResult<&str, BinOp> + '_ {
    move |input| {
        let (input, next) = bin_op(input)?;
        if ops.contains(&next) {
            Ok((input, next))
        } else {
            Err(Err::Error(Error::from_error_kind(input, ErrorKind::Tag)))
        }
    }
}

fn expression(input: &str) -> IResult<&str, Expr> {
    terminated(
        expression_cond,
        pair(multispace0, eof),
    )(input)
}

// Right assoc.
fn expression_cond(input: &str) -> IResult<&str, Expr> {
    let (input, first) = expression_or(input)?;
    let (input, extra) = opt(tuple((
        token(Token::Question),
        expression_cond,
        token(Token::Colon),
        expression_cond,
    )))(input)?;
    let expr = if let Some((_, second, _, third)) = extra {
        Expr::Cond(Box::new(first), Box::new(second), Box::new(third))
    } else {
        first
    };
    Ok((input, expr))
}

fn expression_or(input: &str) -> IResult<&str, Expr> {
    left_assoc(bin_op_any(&[BinOp::Or]), expression_and, Expr::new_bin)(input)
}

fn expression_and(input: &str) -> IResult<&str, Expr> {
    left_assoc(bin_op_any(&[BinOp::And]), expression_equal, Expr::new_bin)(input)
}

fn expression_equal(input: &str) -> IResult<&str, Expr> {
    left_assoc(bin_op_any(&[BinOp::Eq, BinOp::Ne]), expression_not_equal, Expr::new_bin)(input)
}

fn expression_not_equal(input: &str) -> IResult<&str, Expr> {
    left_assoc(bin_op_any(&[BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge]), expression_add, Expr::new_bin)(input)
}

fn expression_add(input: &str) -> IResult<&str, Expr> {
    left_assoc(bin_op_any(&[BinOp::Add, BinOp::Sub]), expression_mult, Expr::new_bin)(input)
}

fn expression_mult(input: &str) -> IResult<&str, Expr> {
    left_assoc(bin_op_any(&[BinOp::Mult, BinOp::Div, BinOp::Mod]), expression_neg, Expr::new_bin)(input)
}

fn expression_neg(input: &str) -> IResult<&str, Expr> {
    alt((
        preceded(token(Token::Neg), expression_neg).map(|e| Expr::Neg(Box::new(e))),
        expression_simple,
    ))(input)
}

fn expression_simple(input: &str) -> IResult<&str, Expr> {
    alt((
        token(Token::N).map(|_| Expr::N),
        number.map(Expr::Const),
        delimited(token(Token::LParen), expression_cond, token(Token::RParen)),
    ))(input)
}


#[cfg(test)]
mod tests {
    use super::*;

    fn refmt(s: &str) -> String {
        let e = expression(s).unwrap().1;
        untyped(&e, 0).to_string()
    }
    #[test]
    fn expr_precedence() {
        assert_eq!(
            refmt("1 ? 2 + 3 : n < 0 ? 6 + 2 : 2 + 3 * 4 - 2 % 5"),
            "if 1 != 0 { 2 + 3 } else if n < 0 { 6 + 2 } else { 2 + 3 * 4 - 2 % 5 }"
        );
        assert_eq!(
            refmt("1 ? 2 : (3 ? 4 : 5)"),
            "if 1 != 0 { 2 } else if 3 != 0 { 4 } else { 5 }"
        );
        assert_eq!(
            refmt("(1 ? 2 : 3) ? 4 : 5"),
            "if if 1 != 0 { 2 } else { 3 } != 0 { 4 } else { 5 }"
        );
        assert_eq!(
            refmt("(1 + 2) + 3"),
            "1 + 2 + 3"
        );
        assert_eq!(
            refmt("1 + (2 + 3)"),
            "1 + (2 + 3)"
        );
        assert_eq!(
            refmt("1 + (2 * (3 + 4))"),
            "1 + 2 * (3 + 4)",
        );
        assert_eq!(
            refmt("1 < 2 || (3 < 4 && 5 <= 6)"),
            "1 < 2 || 3 < 4 && 5 <= 6"
        );
        assert_eq!(
            refmt("1 + 2 * 3"),
            "1 + 2 * 3",
        );
        assert_eq!(
            refmt("1 * 2 + 3"),
            "1 * 2 + 3",
        );
    }
    #[test]
    fn expr_bool() {
        assert_eq!(
            refmt("!!!n"),
            "!!(n == 0)"
        );
        assert_eq!(
            refmt("!!!(n > 1)"),
            "!!!(n > 1)"
        );
    }
}
