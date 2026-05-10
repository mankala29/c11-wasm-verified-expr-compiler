use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Num(i32),
    Var(String),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn num(n: i32) -> Self {
        Expr::Num(n)
    }

    pub fn var(x: &str) -> Self {
        Expr::Var(x.to_string())
    }

    pub fn add(a: Expr, b: Expr) -> Self {
        Expr::Add(Box::new(a), Box::new(b))
    }

    pub fn sub(a: Expr, b: Expr) -> Self {
        Expr::Sub(Box::new(a), Box::new(b))
    }

    pub fn mul(a: Expr, b: Expr) -> Self {
        Expr::Mul(Box::new(a), Box::new(b))
    }

    pub fn let_(x: &str, val: Expr, body: Expr) -> Self {
        Expr::Let(x.to_string(), Box::new(val), Box::new(body))
    }

    /// Returns true if every Var in the expression is bound by an enclosing Let.
    pub fn well_scoped(&self) -> bool {
        self.well_scoped_with(&HashMap::new())
    }

    fn well_scoped_with(&self, env: &HashMap<String, ()>) -> bool {
        match self {
            Expr::Num(_) => true,
            Expr::Var(x) => env.contains_key(x),
            Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) => {
                a.well_scoped_with(env) && b.well_scoped_with(env)
            }
            Expr::Let(x, val, body) => {
                if !val.well_scoped_with(env) {
                    return false;
                }
                let mut env2 = env.clone();
                env2.insert(x.clone(), ());
                body.well_scoped_with(&env2)
            }
        }
    }
}
