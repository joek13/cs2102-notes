/-
A proposition is a mathematical assertion, which may be true or false.
Terms make up a proposition in predicate logic.

Terms are references: they *refer* to a "referent."
In lean, terms are evaluated to yield values.

LEAN has four basic types of terms:
- literal terms
- identifiers
- lambda expressions (which are just another kind of literal term)
- application expressions

At its most fundamental level, LEAN is a type checker.

Consider two types S and T.

S→T is a type itself—specifically, the type of functions that transform from S to T.
In other words, they take S as an input and return T as an output.
-/

def greater_than_three: ℕ → bool := λ n : ℕ, n > 3

#check greater_than_three 
#eval greater_than_three 2 -- application term: we are applying a function to an argument
#check greater_than_three 2 -- as we can see, the type of the application is the return type of the function we've applied

def plus_one: ℕ → ℕ := λ n: ℕ, n + 1

#check plus_one
#eval plus_one 2

-- All equivalent eval results
#eval (λ n, n+1) 2
#eval 2 + 1
#eval 3


-- Challenge: a function that returns a function
-- The first function takes an argument, and the second function takes an argument which it adds to the argument of the first function
-- In other words, it adds the two arguments
def add: ℕ → ℕ → ℕ := λ a b, a + b
-- alternatively:
def add_alt: ℕ → (ℕ → ℕ) := λ a, (λ b, a + b)

#eval (add 3) 3
#eval (add_alt 3) 2

def add3 := add 3

#eval add3 2

-- Recall: the → operation is right-associative; i.e.
-- ℕ → ℕ → ℕ = ℕ → (ℕ → ℕ)

-- Function application is left-associative; i.e.
-- add 3 2 = (add 3) 2

-- "Partial evaluation"—providing only some arguments to a function, returning a new function which takes the remaining unsupplied arguments
-- e.g.

def add_ten := add 10

#check add_ten -- ℕ → ℕ
#eval add_ten 20

-- let's learn about match statements
-- make a boolean negation function
def neg_bool : bool → bool := 
    λ b : bool,
        match b with
        | tt := ff
        | ff := tt
        end

-- shorthand for a function which matches:

def neg_bool' : bool → bool 
    | tt := ff
    | ff := tt

def my_xor : bool → bool → bool :=
    λ a b : bool,
        a ≠ b

def sullivan_xor : bool → bool → bool :=
    λ a b,
        match a, b with 
        | tt, tt := ff
        | ff, ff := ff
        | _, _ := tt
        end

#eval my_xor tt ff
#eval my_xor ff ff
#eval my_xor tt tt

def bool_identity := λ x, neg_bool (neg_bool x)

#eval bool_identity tt