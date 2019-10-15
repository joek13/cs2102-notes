/-
Notes 10/14/2019 
-/

/-
Today, we "turn a corner"—moving from fragmented predicate logic to propositional logic.

Propositional logic is a simple formal language.

Syntactic factors of propositional logic:

only two literal values:
- pTrue
- pFalse

propositional variables (like x,y,z)

oeprators (which are really literal terms):
- pAnd, pOr, pNot

application expressions:
- pNot x, pAnd x y

example:
- pOr x (pAnd y z)


pNot x ≡ ¬x
pAnd x y ≡ x ∧ y
pOr x y ≡ x ∨ y

We're living within the world of boolean algebra
- an algebra with only two values: tt and ff

Evaluation takes you from variable expressions to truthy/falsey literals
-/