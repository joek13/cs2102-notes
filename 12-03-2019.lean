-- Notes 12/03/2019

/-
Continuing our journey of learning to prove propositions of the form P ∨ Q
-/

axiom Q : Prop
axiom q : Q -- axiomatically accept a proof of Q

axiom P : Prop

example : P ∨ Q :=
begin
    apply or.inr q
end

example : false ∨ Q :=
begin
    apply or.inr q
end

example : 0 = 1 ∨ 2 = 2 :=
begin
    apply or.inr,
    apply rfl,
end

example : 0 = 1 ∨ 2 = 2 := or.intro_right _ rfl

#check @or.intro_right
#check @or.inr -- shorthand version

example : P ∨ Q := or.intro_right P q

-- classical vs. constructive logic
example : P ∨ ¬P := sorry -- excluded middle: we can't prove this in constructive logic

-- in constructive logic, if we don't have a proof of P, but we also don't have a proof of ¬P, we can't construct a proof of P ∨ ¬P
-- c.f. the P=NP problem. We don't have a proof that P = NP, but we also don't have a proof that P != NP.

-- the excluded middle is a valid form of reasoning in classical logic
axiom excluded_middle : ∀ (P : Prop), P ∨ ¬P

example : P ∨ ¬P := excluded_middle P

example : P ∨ ¬P := 
begin
    apply classical.em
end

example : ∀ (P : Prop), ¬ ¬ P → P := 
begin
    assume P,
    assume nnp,
    cases (classical.em P) with hp hnp, -- we rely upon the law of the excluded middle to achieve this proof
    exact hp,
    contradiction,
end

/-
Proof by negation: when we want to show ¬P
Proof by negation: to prove ¬P, we show that P leads to a contradiction.

Assume P, show contradiction gives us ¬P
-/

/-
Proof by contradiction: prove P by showing ¬P → false (¬¬P → P)

If we want a proof that P is true, assume P is false, and show it leads to a contradiction

I.e. show that ¬P → false
i.e. ¬¬P holds

If we have the law of the excluded middle, we can show ¬¬P → P

Assume ¬P, show contradiction gives us P
-/

axiom Rational : nat → Prop

example : ¬¬(Rational 2) → Rational 2 :=
begin
    assume nnrt,
    cases (classical.em (Rational 2)),
    exact h,
    contradiction,
end