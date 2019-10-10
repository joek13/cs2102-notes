/-
 * Give examples of terms of various types, including basic data types and function types.
 * To answer the function-type-related questions, you really must know how to write lambda expressions.
-/

/-
Three types of terms:
-/

/-
literal terms → e.g. 3, "hello", tt, lambda expressions
-/

#eval 3
#eval tt
#eval "hello"
#check (λ (n : ℕ), n+2) -- lambda expressions are also literal terms

/-
identifier terms: terms which "name" other terms
-/

def n := 3

#eval n -- these lines produce the same results
#eval 3

-- identifier terms in lean are referentially transparent, which means that we can safely replace each term with its referent without changing meaning

/-
What happens when we evaluate these terms:
- literal terms: evaluate to the literal itself (e.g. `#eval 3` returns `3`)
- identifier terms: evaluate ("resolve") to the terms they reference (e.g. `#eval n` returns `3` when n was defined as 3)

Last term type:
- application terms (e.g. the application of f to x, `(f x)`)
-/

/- Lambda expressions: define anonymous functions -/

def sum_nats : nat → nat → nat := λ a : nat, λ b : nat, a+b -- a function which takes two arguments, or, a function which takes the first argument and returns a function which takes the second argument

def add_five := sum_nats 5
#check add_five -- nat → nat