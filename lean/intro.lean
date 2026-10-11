inductive Expression : Type where
  | var   : String → Expression
  | const : Int → Expression
  | add   : Expression → Expression → Expression
  | mul   : Expression → Expression → Expression
  deriving Repr

open Expression

-- Trivial example of using the type constructors.

#eval add (mul (const 2) (var "x" )) (var "y")

-- Simplification example.

def simplify1 (expr : Expression) : Expression :=
  match expr with
  | add (const m) (const n) => const (m + n)
  | mul (const m) (const n) => const (m * n)
  | add (const 0) x         => x
  | add x (const 0)         => x
  | mul (const 0) _         => const 0
  | mul _ (const 0)         => const 0
  | mul (const 1) x         => x
  | mul x (const 1)         => x
  | _                       => expr

def simplify (expr : Expression) : Expression :=
  match expr with
  | add e1 e2 => simplify1 (add (simplify e1) (simplify e2))
  | mul e1 e2 => simplify1 (mul (simplify e1) (simplify e2))
  | _         => simplify1 expr

-- Example.

def e : Expression :=
  add (mul (add (mul (const 0) (var "x")) (const 1)) (const 3)) (const 12)

#eval simplify e

-- Lexical analysis.                                                         *)
def matches_ (s : String) (c : Char) : Bool :=
  s.contains c

def space        := matches_ " \t\n\r"
def punctuation  := matches_ "()[]{},"
def symbolic     := matches_ "~`!@#$%^&*-+=|\\:;<>.?/"
def numeric      := matches_ "0123456789"
def alphanumeric := matches_ "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

def lexwhile (prop : Char → Bool) (inp : List Char) : String × List Char :=
  match inp with
  | c :: cs => 
    if prop c then 
      let (tok, rest) := lexwhile prop cs
      (c.toString ++ tok, rest)
    else 
      ("", inp)
  | [] => ("", inp)

partial def lex (inp : List Char) : List String :=
  let (_, trimmed) := lexwhile space inp
  match trimmed with
  | [] => []
  | c :: cs =>
    let prop := 
      if alphanumeric c then alphanumeric
      else if symbolic c then symbolic
      else fun _ => false
    let (toktl, rest) := lexwhile prop cs
    (c.toString ++ toktl) :: lex rest

#eval lex "2*((var_1 + x') + 11)".toList
#eval lex "if (*p1-- == *p2++) then f() else g()".toList

-- Parsing.

def isNumericToken (tok : String) : Bool :=
  !tok.isEmpty && tok.toList.all numeric

mutual
  def parse_expression (i : List String) : Except String (Expression × List String) :=
    match parse_product i with
    | Except.error e => Except.error e
    | Except.ok (e1, "+" :: i1) =>
      match parse_expression i1 with
      | Except.ok (e2, i2) => Except.ok (add e1 e2, i2)
      | Except.error e => Except.error e
    | Except.ok (e1, i1) => Except.ok (e1, i1)

  def parse_product (i : List String) : Except String (Expression × List String) :=
    match parse_atom i with
    | Except.error e => Except.error e
    | Except.ok (e1, "*" :: i1) =>
      match parse_product i1 with
      | Except.ok (e2, i2) => Except.ok (mul e1 e2, i2)
      | Except.error e => Except.error e
    | Except.ok (e1, i1) => Except.ok (e1, i1)

  def parse_atom (i : List String) : Except String (Expression × List String) :=
    match i with
    | [] => Except.error "Expected an expression at end of input"
    | "(" :: i1 =>
      match parse_expression i1 with
      | Except.ok (e2, ")" :: i2) => Except.ok (e2, i2)
      | Except.ok _ => Except.error "Expected closing bracket"
      | Except.error e => Except.error e
    | tok :: i1 =>
      if isNumericToken tok then
        -- String.toInt! parses a string to an Int, panicking if it fails 
        -- (Safe here because we verified it with isNumericToken)
        Except.ok (const tok.toInt!, i1)
      else
        Except.ok (var tok, i1)
end

def make_parser (pfn : List String → Except String (Expression × List String)) (s : String) : Except String Expression :=
  match pfn (lex s.toList) with
  | Except.error msg => Except.error msg
  | Except.ok (expr, []) => Except.ok expr
  | Except.ok (_, _ :: _) => Except.error "Unparsed input"

def parser : String → Except String Expression := 
  make_parser parse_expression

#eval! parser "x+1"
#eval! parser "(x1 + x2 + x3) * (1 + 2 + 3 * x + y)"

-- Conservatively bracketing first attempt at printer.
def string_of_exp1 (e : Expression) : String :=
  match e with
  | var s     => s
  | const n   => toString n
  | add e1 e2 => "(" ++ string_of_exp1 e1 ++ " + " ++ string_of_exp1 e2 ++ ")"
  | mul e1 e2 => "(" ++ string_of_exp1 e1 ++ " * " ++ string_of_exp1 e2 ++ ")"

-- Register it with Lean's native ToString type class
instance : ToString Expression where
  toString := string_of_exp1

#eval! toString (parser "x+3*y")

-- Somewhat better attempt.
def string_of_exp2 (pr : Nat) (e : Expression) : String :=
  match e with
  | var s => s
  | const n => toString n
  | add e1 e2 => 
      let s := (string_of_exp2 3 e1) ++ " + " ++ (string_of_exp2 2 e2)
      if 2 < pr then "(" ++ s ++ ")" else s
  | mul e1 e2 =>
      let s := (string_of_exp2 5 e1) ++ " * " ++ (string_of_exp2 4 e2)
      if 4 < pr then "(" ++ s ++ ")" else s

instance : ToString Expression where
  toString := string_of_exp2 0

-- Examples
#eval! toString (parser "x+3*y")
#eval! toString (parser "(x+3)*y")
#eval! toString (parser "1 + 2 + 3")

-- Example shows the problem
#eval! toString (parser "(x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10) * (y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8 + y9 + y10)")
