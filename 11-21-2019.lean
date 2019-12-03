-- 11/21/2019 - natural deduction

variables P Q R : Prop

-- two different ways to solve proofs including "forall"

-- forall introduction: given a proof of Q for an arbitrary value of type P, we can conclude that Q holds "for all" P
    -- i.e. ∀ (p : P), Q


example : ∀ (p : P), Q :=
    λ (hp : P),
        sorry

example : ∀ (p : P), Q :=
begin
    assume hp,
    sorry
end

example : (∀ (p : P), Q) → P → Q :=
begin
    assume pq,
    exact pq
end


example : (∀ (p : P), Q) → P → Q :=
    λ (pq : ∀ (p : P), Q), -- forall "introduction" - we assume an arbitrary value using a lambda expression
        λ (hp : P),        -- assume P
            (pq hp)        -- forall "elimination" - apply our "for all" proof to our hypothesis of p


example : (∀ (p : P), Q) → P → Q := id

-- What's the f word? Just kidding. Function!

-- Proof that X → Y is really just a function that takes an argument that is a proof of X, and spits out a proof of Y

example : (P ∧ Q) → P := and.elim_left
example : (P ∧ Q) → Q := and.elim_right

-- = introduction
-- for any value of type α a, a=a
-- (eq.refl)

variable L : P → Prop


-- = elimination rule : eq.subst
-- given a proof that a = b, we derive a proof that P a implies P b


example : ∀ (a b : P), (a = b) → (L a → L b) := 
begin 
    assume a b, -- assume a and b of typ eP
    assume heq, -- assume a = b
    apply eq.subst, -- apply equals substitution; new goal: show that a = b
    exact heq, -- assumption.
end

example : ∀ (a b : P), (a = b) → (L a → L b) := λ (a b : P), eq.subst


-- the equals relation has two fundamental properties: reflexivity and substitutability.

-- negation! meet "false."
-- false is a proposition that is never true. it has no proofs.

def f : false → 0 = 1 :=
begin
    assume f,
    apply false.elim,
    exact f,
end

def f' : false → 0 = 1
| x := false.elim x

-- false elimination: we can derive a proof of anything from false

example : ¬(0=1):=
begin
    contradiction,
end