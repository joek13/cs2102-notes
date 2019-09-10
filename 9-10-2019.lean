/-
LEAN operates in "higher-order predicate logic."

Expressions yield values. 
-/

#eval 2

/-
Terms - 
Literal terms - 

We've evaluated this literal expression to yield a value of 2.
Expressions are more general than literals because they can do operations.
Expressions are a part of the language's syntax, while values are not.
-/

#eval 2+2

/-
Types are first-class citizens in lean, which means that they are also terms.
-/

#check nat
#check ℕ

/-
The preceding checks are equivalent. ℕ is obtained by typing "\nat"
-/

#check ff /- false is of type bool -/
#check bool /- bool is of type Type -/
#check Type /- Type is of type.... Type 1?-/

#eval "Hello Lean!"

/-
Identifiers in LEAN are different than variables in imperative programming languages.

Identifier term: a name for another term
-/

def n := 1 -- n is bound to the literal term 1; n is non-mutable

#check 1 -- 1 is of type nat
#check n -- therefore n is also of type nat

def m : ℕ := 1 -- we can also specify the type explicitly (Lean will attempt to infer if type is elided)

-- def k : ℕ := "hey!"
-- the above line is commented out as it is rejected by the type-checker

/-
Literal terms - evaluating gives you the literal itself
Identifier terms - evaluating gives you the value to which it is bound ("resolves")

Up until now, we've addressed literal terms, identifier terms, and now: functions types
-/

#check bool → bool -- a function that goes from boolean to boolean

#check nat → nat -- a unary function (one input)
#check bool → bool → bool -- a binary function (two inputs)

#check nat → nat → nat -- also binary
#check nat → (nat → nat) -- the arrow is right-associative (these two are equivalent)
-- (a function that maps from nat to a nat→nat function)

-- The next line is NOT equivalent to the preceding two
#check (nat → nat) → nat -- a function that maps from a nat→nat function to a single nat

/-
Lean functions that take multiple inputs are technically single-input functions: 
The first function takes a single input, and returns a function that takes a single input (i.e. the second input).
-/
 
def always_false : bool → bool := 
    λ x: bool, ff -- we define a lambda function that takes a single boolean argument and returns false

