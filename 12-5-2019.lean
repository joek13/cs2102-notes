-- Notes 12/5/2019

/- Talking about logics

We don't have just one logic; we have many
- predicate logic
    - the language of predicate logic: variables, functions, 
- propositional logic
- some other logics (temporal logic)


- functions
- inductive types

types we have:
- true
- false
- a = b
    - introduction rule: eq.refl
- P ∧ Q
    - introduction rule: and.intro
- P ∨ Q
    - introduction rule: or.intro_left / or.intro_right
- P → Q
- P ↔ Q
    - introduction rule: iff.intro
- ¬P
- ∀ (p : P), Q
- ∃ (p: P), Q
-/


/-

Sample propositions:

If there's some P everyone likes, then everyone likes some P
-/

inductive Person : Type
inductive Likes : Person → Person → Prop

example : (∃ (p : Person), ∀ (q : Person), Likes q p) → ∀ (q : Person), (∃ (p : Person), Likes q p) :=
begin
    assume someone_everyone_likes,
    assume q,
    apply exists.elim someone_everyone_likes,
    assume a,
    assume hypothesis,
    have q_likes_a := hypothesis q,
    apply exists.intro,
    exact q_likes_a,
end

axiom f : false

example : (∃ (p : Person), ∀ (q : Person), Likes q p) → ∀ (q : Person), (∃ (p : Person), Likes q p) :=
begin
    assume h,
    assume p,
    -- "identify a witness"
    cases h with w pf,
    apply exists.intro w _,
    exact pf p
end


inductive jlist (α : Type) : Type 
| nil : jlist
| cons (a : α) (t : jlist) : jlist

def len {α : Type} : jlist α → nat
| (jlist.nil α):= 0
| (jlist.cons a t) := nat.succ (len t)



example : (∃ (p : Person), ∀ (q : Person), Likes q p) → ∀ (q : Person), (∃ (p : Person), Likes q p) :=
begin
    assume h,
    assume p,
    cases h with w pf,
    apply exists.intro w (pf p)
end

-- "Proof of an exists is just a pair"
    -- that pair is "a witness" and "a proof that witness satisfies p"

def even : nat → Prop := λ (q : nat), ∃ (n : nat), n * 2 = q

theorem two_even : even 2 :=
begin
    exact exists.intro 1 (eq.refl _),
end

example : ∀ (b : bool), bor b tt = tt := 
begin
    assume b,
    cases b,

    exact eq.refl tt,
    exact eq.refl tt,
end

example : ∀ (n : ℕ), n = 0 ∨ n ≠ 0 :=
begin
    assume n,
    cases n with p z,
    apply or.inl,
    refl,

    apply or.inr,
    apply not.intro,
    assume ridiculous,
    cases ridiculous,
end

example : ∀ (n : ℕ), n = 0 ∨ n ≠ 0 := λ (n : nat), classical.em _