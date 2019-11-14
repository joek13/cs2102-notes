/-
Notes for 11-07-2019.lean
-/

namespace test
-- The and'' proposition is really just like a product inductive type
inductive and'' (α β : Prop) : Prop
| intro : α → β → and''

-- but over the universe of Prop rather than of Type

inductive prod' (α β : Type) : Type
| pair : α → β → prod'

structure and (a b : Prop) : Prop :=
    intro :: (left : a) (right : b)

def and.elim_left {α β : Prop} : and α β → α 
| (and.intro a b) := a

def and.elim_right {α β : Prop} : and α β → β
| (and.intro a b) := b

end test

def P1 : Prop := 0 = 0
def P2 : Prop := 1 = 1
def p1 : P1 := eq.refl 0

def P1_and_P2 := P1 ∧ P2

theorem pf : P1_and_P2 :=
begin
    apply and.intro,
    apply eq.refl,
    apply eq.refl
end

inductive Person
| harsh
| joe
| will

inductive friends : Person → Person → Prop
| refl : ∀ (a : Person), friends a a
| symm : ∀ (a b : Person), (friends a b) → (friends b a)
| trans : ∀ (a b c : Person), (friends a b) → (friends b c) → (friends a c)

theorem joe_is_friends_with_self : friends Person.joe Person.joe :=
begin
    apply friends.refl
end

open Person 
theorem if_harsh_then_harsh : (friends harsh joe) → (friends joe harsh) :=
begin
    apply friends.symm,
end

def transitive' {α : Type} (r : α → α → Prop) : Prop := ∀ (a b c : α), r a b → r b c → r a c

theorem friends_transitive : transitive' friends :=
begin
    unfold transitive',
    assume (a b c),
    assume ab bc,
    exact friends.trans a b c ab bc,
end

/-
Prove 0=0.

Proof: Equality is reflexive. this means that for any value a of any type α, a = a.

∀ {T : Type}, t → t = t

We apply this axiom to 0 in particular, to derive a proof that 0=0. 
-/