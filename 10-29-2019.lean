-- Notes 10/29/2019
/-
Moving from propositional logic to predicate logic

Over what values do variables range in prop. logic? → true and false
In predicate logic, variables range over arbitrary domains.

∀ p: Person, ∃ q: Person, p likes q
"For every person p, there exists a person q such that p likes q" → "everyone likes someone"

∃ p: Person, ∀ q: Person, p likes q
"someone likes everyone"

∃ p: Person, ∀ q: Person, ¬ (q likes p)
"there exists someone who everybody dislikes"

"everyone dislikes someone"
∀ p, ∃ q, ¬ likes p q

Propositions & existential quantifiers

(∃ p, ∀ q, ¬likes q p) → ¬likes p p
if everybody dislikes p, then p dislikes themselves

We need a way to reason with predicate logic and propositions

How do we verify whether a predicate logic propositions are true?
    Proof!

We can use our logical rules of deduction to reason about whether proofs are valid

IFF introduction:
If we have a proof of P and a proof of Q, we have a proof of P ∧ Q
If we have a proof of P ∧ Q, we have a proof of P and we have a proof of Q
If we need to prove P ↔ Q, it suffices to prove P ⇒ Q and Q ⇒ P

Syllogism:
To prove P ⇒ R, it suffices to show that
P ⇒ Q and Q ⇒ R

Can we automatically prove these?


-/

-- Remember the "day" inductive?
inductive day : Type
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday

def is_weekend : day → bool 
| day.saturday := tt
| day.sunday := tt
| _ := ff

def is_weekday : day → bool := λ d, ¬is_weekend d

inductive emily_is_from_cville : Prop
-- the constructors for this prop are types of proofs
-- these are axioms: they are accepted to be true without further truth
| drivers_license
| passport
| utility_bill
open emily_is_from_cville
def a_proof : emily_is_from_cville := drivers_license -- axiomatically, we accept that a drivers' license is sufficient to conclude that emily is from cville
theorem a_proof' : emily_is_from_cville := passport