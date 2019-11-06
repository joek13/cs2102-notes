-- Notes 10/22/2019

/-
Quick recap:

pEval e i

e is of type pExp
i is of type (var→bool)
pEval returns a bool

i is a "model" of e if i makes e evaluate to true.

If e is valid, all possible i are models of e.
If e is satisfiable, at least one i exists that is a model of e.
If e is unsatisfiable, no i exists that is a model of e.
-/

import .prop_logic

open prop_logic

def isModel (i : var → bool) (e : pExp) :=
    pEval e i = tt

def valid (e: pExp) :=
    ∀ (i : var → bool),
        isModel i e

def unsatifiable (e : pExp) :=
    ∀ (i : var → bool),
        ¬isModel i e

def satisfiable (e : pExp) :=
    ∃ (i : var → bool),
        isModel i e

#reduce valid (pTrue)

/-
And introduction:

given P, Q we can deduce that (P ∧ Q) is true

The converse is also true:

given (P ∧ Q), we can deducr P, Q
-/

def puzzle := ∃ (e : pExp), (satisfiable e) ∧ ¬ (valid e)
-- X satisfies the puzzle

/-
Why logic?

We can take an argument in natural language, convert it into a formal language, and verify the truth of the argument using simple rules

R = it's raining
W = the streets are wet

(R ⇒ W) ⇒ (W ⇒ R)

"if it is true that if it is raining, the streets are wet, then if the streets are wet, it is raining"
false: someone could've dumped water on the sidewalk
R ⇒ W does not imply W ⇒ R

What about
(R ⇒ W) ⇒ (¬W ⇒ ¬R)

or

(R ⇒ W) ⇒ (¬R ⇒ ¬W)

R W expr
F F  T
F T  F
T F  T
T T  T
-/


/-
-- If the premise of an implication is false, the whole implication is false

and introduction:
P ⇒ (Q ⇒ P ∧ Q)

and_elim_left:
P ∧ Q ⇒ P

and_elim_right:
P ∧ Q ⇒ Q

or_intro_left:
P ⇒ P ∨ Q
or_intro_right:
Q ⇒ P ∨ Q
-/
