/-
There are two key things we do with proofs.

(1) We build them
(2) We use them

In logic, the basic rules for building,
or constructing, proofs go by the name
of introduction rules. The basic rules
for using proofs are called elimination
rules.

Each *form* of proposition has its own
introduction and elimination rules. For
example, to build a proof of P ∧ Q, one
must use the introduction rule for and,
while using a proof of P ∧ Q relies on
the two elimination rules, which serve
to extract from a proof of P ∧ Q a proof
of P or a proof of Q.

In this class, we assume (P Q : Prop), 
(T : Type), (x y : T) then summarize, 
review,  and practice using the rules 
to build and use proofs of these forms:

- ∀ (p : P), Q  [Q usually a predicate]
    - introduction: making arbitrary assumption 
    - elimination: take the predicate for any value of P you want
- x = y ⇒ eq.refl _ _
    - introduction: eq.refl _ _
    - elimination: 
- P → Q 
    - introduction: 
- P ∧ Q 
    - introduction: and.intro
    - elimination: and.elim_left and and.elim_right
- ∃ (x : P), Q  [Q usually a predicate]

A key to understanding how to build
proofs is that it's a top-down and
recursive process. For example, to
build a proof of ∀ (p : P), Q, we
use the introduction rule for ∀. It
tells us to assume that p is some
arbitrary but specific value of type
P, and then to prove Q for that p.
To do this, we recursively apply 
our approach to building proofs to
build a proof of Q, but now within
a context in which we can use the
assumption that p is some specific
value of type P. We now repeat the
same process: (1) ask what form is 
Q; (2) choose an introduction rule
for that form of proposition. Often
we need smaller proofs to apply the
introduction rules, and for this, we
use proofs we have already built or
assumed, using elimination rules as
necessary.
-/

def no_largest_nat := ¬∃ (n : nat), ∀ (k : nat), n > k

def append {α : Type} : (list α) → α → (list α) 
| list.nil a := list.cons a list.nil
| (list.cons b t) a := list.cons b (append t a)

def list_reverse {α : Type} : (list α) → (list α)
| list.nil := list.nil
| (list.cons a t) := append (list_reverse t) a

/-
Forall introduction

Assume that you have an arbitrary but specific value of the quantified type,
(p : P), then prove Q for p.

Example: prove "all balls are green"

Step 0: formalize the proposition

∀ (b : Ball), Green b

Step 1: We start by assuming
that b0 is an arbitrary but specific ball,
and now all that remains to be proved is
Green b.

Formally, we just need to prove Green b0

Example: prove ∀ (n : ℕ), n = n.

In english: prove that, for all natural numbers n, n = n.

Proof.
Assume an arbitrary but specific natural number n. What remains to be shown is that n=n.
By the reflexive property of equality, any natural number equals itself, so n = n.
Therefore, for all natural numbers n, n = n.
-/

theorem pf : ∀ (n : nat), n = n := eq.refl

#check ∀ (k : ℕ), k = k

example : ∀ (n : ℕ), nat.pred (nat.succ n) = n :=
begin
    assume n0,
    apply eq.refl
end

/- ∀ elimination
Given a proof that every ball is green, we can conclude that any ball of your choice is green

If every ball is green, then we can prove that b0 is green

Proof:

Assume that every ball is green.
Assume b0 is a ball.
By our assumption that every ball is green, b0 is green.
-/

example : ((∀ (n : nat), n = n) → (2 = 2)) := (λ (pf), pf _)

inductive Ball : Type
| mk : Ball

inductive Green : Ball → Prop

def to_prove := (∀ (b : Ball), Green b) → (∀ (b0 : Ball), Green b0)

example : to_prove := λ h, λ b0, h b0
example : to_prove := id
example : to_prove :=
begin
    unfold to_prove,
    assume a,
    assume b0,
    apply a b0
end