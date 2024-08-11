// Reference implementation:
// https://github.com/autotools-mirror/gettext/blob/master/gettext-runtime/intl/plural.y

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
            Add | Sub | Mult | Div | Mod | Eq | Ne | Gt | Ge | Lt | Le => Int,
            And | Or => Bool,
        }
    }
    fn fmt_precedence(&self) -> u32 {
        use BinOp::*;
        match self {
            Or => 1,
            And => 2,
            Eq | Ne => 3,
            Gt | Ge | Lt | Le => 4,
            Add | Sub => 5,
            Mult | Div | Mod => 6,
            // Unary Not would be 7
        }
    }
}

const PRECEDENCE_NOT: u32 = 7;

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
        match ty {
            Some(ty) => {
                let my = e.get_type();
                if my == ty {
                    write!(f, "{}", untyped(e, precedence))?;
                } else {
                    match ty {
                        Bool => {
                            let paren = precedence > BinOp::Ne.fmt_precedence();
                            if paren { write!(f, "(")?; }
                            write!(f, "{} != 0", untyped(e, BinOp::Ne.fmt_precedence()))?;
                            if paren { write!(f, ")")?; }
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
                                let paren = precedence > PRECEDENCE_NOT;
                                if paren { write!(f, "(")?; }
                                write!(f, "!{}", untyped(e, PRECEDENCE_NOT))?;
                                if paren { write!(f, ")")?; }
                            }
                            // !(a != 0) => a == 0
                            Int => {
                                let paren = precedence > BinOp::Eq.fmt_precedence();
                                if paren { write!(f, "(")?; }
                                write!(f, "{} == 0", untyped(e, BinOp::Eq.fmt_precedence()))?;
                                if paren { write!(f, ")")?; }
                            }
                        }
                    }
                    Binary(e1, op, e2) => {
                        let ty = op.arg_type();
                        let prec = op.fmt_precedence();
                        let paren = precedence > prec;
                        if paren { write!(f, "(")?; }
                        write!(f, "{} {op} {}", typed(e1, ty, prec), typed(e2, ty, prec + 1))?;
                        if paren { write!(f, ")")?; }
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Token {
    LParen, RParen,
    Op(BinOp),
    Neg,
    Question, Colon,
    Number(u32),
    N,
}

fn next_token(input: &str) -> IResult<&str, Token> {
    let (input, _) = multispace0(input)?;
    use Token::*;
    use BinOp::*;
    let res = alt((
        tag("&&").map(|_| Op(And)),
        tag("||").map(|_| Op(Or)),
        tag("==").map(|_| Op(Eq)),
        tag("!=").map(|_| Op(Ne)),
        tag(">=").map(|_| Op(Ge)),
        tag("<=").map(|_| Op(Le)),
        map_res(digit1, |n: &str| { let n = n.parse()?; Ok::<_, std::num::ParseIntError>(Number(n)) }),
        char('n').map(|_| N),
        char('(').map(|_| LParen),
        char(')').map(|_| RParen),
        char('+').map(|_| Op(Add)),
        char('-').map(|_| Op(Sub)),
        char('*').map(|_| Op(Mult)),
        char('/').map(|_| Op(Div)),
        char('%').map(|_| Op(Mod)),
        char('!').map(|_| Neg),
        char('>').map(|_| Op(Gt)),
        char('<').map(|_| Op(Lt)),
        char('?').map(|_| Question),
        char(':').map(|_| Colon),
    ))(input)?;
    Ok(res)
}

fn number() -> impl Fn(&str) -> IResult<&str, u32> {
    move |input| {
        let (input, next) = next_token(input)?;
        if let Token::Number(n) = next {
            Ok((input, n))
        } else {
            Err(Err::Error(Error::from_error_kind(input, ErrorKind::Tag)))
        }
    }
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

macro_rules! expression_left_assoc {
    ($name:ident, $operator:expr, $next:ident) => {
        fn $name<'i>(input: &str) -> IResult<&str, Expr> {
            let (input, expr1) = $next(input)?;
            let mut expr1 = Some(expr1);
            let (input, expr) = fold_many0(pair($operator, $next),
                    || expr1.take().unwrap(),
                    |e1, (op, e2)| Expr::Binary(Box::new(e1), op, Box::new(e2))
                )(input)?;
            Ok((input, expr))
        }
    };
}

fn bin_op(op: BinOp) -> impl Fn(&str) -> IResult<&str, BinOp> {
    move |input| {
        map(token(Token::Op(op)), |_| op)(input)
    }
}

fn bin_op_any(ops: &[BinOp]) -> impl Fn(&str) -> IResult<&str, BinOp> + '_ {
    move |input| {
        let (input, next) = next_token(input)?;
        if let Token::Op(op) = next {
            if ops.contains(&op) {
                return Ok((input, op));
            }
        };
        Err(Err::Error(Error::from_error_kind(input, ErrorKind::Tag)))
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

expression_left_assoc!{expression_or, bin_op(BinOp::Or), expression_and}
expression_left_assoc!{expression_and, bin_op(BinOp::And), expression_equal}
expression_left_assoc!{expression_equal, bin_op_any(&[BinOp::Eq, BinOp::Ne]), expression_not_equal}
expression_left_assoc!{expression_not_equal, bin_op_any(&[BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge]), expression_add}
expression_left_assoc!{expression_add, bin_op_any(&[BinOp::Add, BinOp::Sub]), expression_mult}
expression_left_assoc!{expression_mult, bin_op_any(&[BinOp::Mult, BinOp::Div, BinOp::Mod]), expression_neg}

fn expression_neg(input: &str) -> IResult<&str, Expr> {
    alt((
        preceded(token(Token::Neg), expression_neg).map(|e| Expr::Neg(Box::new(e))),
        expression_simple,
    ))(input)
}

fn expression_simple(input: &str) -> IResult<&str, Expr> {
    alt((
        token(Token::N).map(|_| Expr::N),
        number().map(|n| Expr::Const(n)),
        delimited(token(Token::LParen), expression_cond, token(Token::RParen)),
    ))(input)
}


#[cfg(test)]
mod tests {
    use super::*;

    fn tokens(input: &str) -> IResult<&str, Vec<Token>> {
        terminated(
            many0(next_token),
            pair(multispace0, eof),
        )(input)
    }

    #[test]
    fn tokenize() {
        use Token::*;
        use BinOp::*;
        assert_eq!(
            tokens("  (0 + 234 - n == < <= ! !=) ==== ").unwrap().1,
            vec![LParen, Number(0), Op(Add), Number(234), Op(Sub), N, Op(Eq), Op(Lt), Op(Le), Neg, Op(Ne), RParen, Op(Eq), Op(Eq)]
        );
    }

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
    fn expr_neg() {
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
