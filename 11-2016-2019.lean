-- Notes 11/26/2019


-- false is not provable, except from a contradiction
-- if we reach a proof of false, our proposition must be false

-- false also implies anything
example : false → 0 = 1 := false.elim

example : ∀ (P : Prop), false → P := λ (p), λ (f), false.elim f

#check @false.elim

-- If we can show that P → false, then P must not be true
-- No proof could exist for P

axiom P : Prop

example : P → ¬P → false := 
begin
    assume hp,
    assume hnp,
    contradiction
end

example : P → ¬P → false :=
    λ (hp),
        λ (hnp),
            (hnp hp)

example : P → ¬ P → 0 = 1 :=
    λ (hp),
        λ (hnp),
            false.elim (hnp hp)

example : P → (P → ¬ P) → false :=
begin
    assume hp,
    assume pnp,
    apply pnp hp,
    exact hp,
end

axiom Q : Prop
axiom q : Q

example : P ∨ Q :=
begin
    apply or.intro_right, -- or.intro_right lets you construct a proof of P ∨ Q from Q
    exact q,
end

axiom excluded_middle : ∀ (P : Prop), P ∨ ¬P 

example : P ∨ ¬P := 
begin
    exact (excluded_middle P),
end

-- or elimination : P ∨ Q → (P → R) → (Q → R) → R
-- if we have P or Q, and P implies R, and Q implies R, then R must be true!!


-- case analysis

axioms
    (R : Prop)
    (p : P)
    (pr : P → R)
    (qr : Q → R)

example : (P ∨ Q) → R :=
begin
    assume pq,
    apply or.elim pq pr qr,
end

example : (P ∨ Q) → R :=
    λ pq,
        match pq with
        | or.inl hp := pr hp
        | or.inr hq := qr hq
        end

example : (P ∨ Q) → R :=
begin
    assume pq,
    cases pq with hp hq,
    apply pr hp,
    apply qr hq,
end