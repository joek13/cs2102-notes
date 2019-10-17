-- Notes 10/17/2019

-- Most of the work for today is in ./prop_logic.lean ./prop_logic_test.lean

/- Notes on operator syntax
Prefix, infix, and postfix

Prefix: (+ 3 5)
Infix: 3 + 5
Postfix (3 5 +)

Functions are supplied in prefix notation
Infix is standard for arithmetic, etc.
Postfix -- accessor operator '.' , subscripting/indexing operator '[]'

Some terms that are relevant to boolean algebra:

- satisfiable -- whether an interpretation exists that makes this true
- unsatisfiable -- no interpretation exists that makes this true
- valid -- the value is true regardless of interpretation

Example:

X ∧ ¬X -- unsatisfiable
X ∨ ¬X -- valid


  x |  y  | (x ∧ y) ∨ (¬y)
 ---+-----+---------------
 tt | tt  | t
 tt | ff  | t
 ff | tt  | f
 ff | ff  | t

 There is one interpretation that makes the expression true, so it is satisfiable
 ... but it's not always true (under any interpretation), so it isn't valid

 Boolean satisfiability problem: given a boolean expression, determine if at least one interpretation exists to make it true
 ... boolean satisfiability problems have O(2^n) worst-case time complexity—an NP-complete problem

 Let's describe these terms in predicate logic

 Unsatisfiable:

 unsat e ↔ ¬ ∃ (i: var → bool), pEval e i = tt         -- "there does not exist an interpretation such that the expression evaluates to true"
 sat e ↔ ¬ unsat e ↔ ∃ (i: var → bool), pEval e i = tt         -- "there exists an interpretation such that the expression evaluates to true"
 valid e ↔ ∀ (i: var → bool), pEval e i = tt                                  -- "for every interpretation, the expression evaluates to true"

-/