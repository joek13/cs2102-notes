-- Notes for 10/31/2019: boooooolean

inductive fuckitwe (α : Type) : Type
| fuckitwe : α → fuckitwe

def harsh := fuckitwe bool


/-
Propositions can be formalized as types, and proofs are just values of those types
-/

/-
Review we define day to be a type.
-/

inductive day : Type
| mon
| tue
| wed
| thu
| fri
| sat
| sun

/-
This is a *computational*, its constructoras define the possible values that we can build of this type
-/

/-
Introducing the begin-end pair
The begin-end pair allows us to incrementally build values 
-/
def d : day := 
begin
    -- lean is in "scripting mode"
    exact day.mon, -- exact must be given an argument which is *exactly* the type of 
end

/-
The defenition d is an assertion that there exists a value of type day
-/

/-
Propositions are formalized as types deriving from Prop.
Constuctors define the values, which we accept as proofs of the proposition
Proofs in Lean are values of logical types
-/
inductive emily_is_from_cville : Prop
| drivers_license
| passport
| utility_bill

inductive false_prop : Prop

open emily_is_from_cville

theorem proof: emily_is_from_cville :=
begin
    exact utility_bill,
end

/-
We can generalize from a specific proposition,
such as the prop that emily is from charlottesville, to
one that allows us to assert that any given person is from
Charlottesville by adding a parameter.
-/

inductive person
| mari
| jose
| jane
| bill

open person

inductive is_from_cville : person → Prop
| proof_for :
    ∀ (p : person), -- for any person p,
        (p = mari) → is_from_cville mari -- if p is mari, then a proof that the person is from charlottesville exists

/-
Proposition with a parameter: a function that returns a proposition.

is_from_cville is a PREDICATE.

Predicates can be thought of as defining properties that apply to the arguments
-/

#check is_from_cville -- function from person → Prop
#check (is_from_cville mari) -- Prop
#check is_from_cville jane
#check is_from_cville bill

/-
Let's create a proof that mari is from cville.
-/
#check is_from_cville.proof_for mari
#check is_from_cville.proof_for jose

theorem mari_is_from_cville: is_from_cville mari :=
begin
    apply is_from_cville.proof_for _ _,
    exact mari,
    exact eq.refl mari -- reflexive equality proof (x = x)
end

/-
Our proof_for constructor effectively allows us to derive a proof that someone is from charlottesville if we have a proof that p = mari
-/

/-
Relations
- can be reflexive (a = a, so an equality relation is reflexive)
- can be symmetric (if a = b, then b = a, so the equality relation is reflexive)

"If I accept a 'likes request' on Facebook, I have to 'like' you back"
"That doesn't exist"
-/

/-
Predicaates are often used to express properties of objects.
-/

inductive is_zero : ℕ → Prop
| zmk : ∀ (n : ℕ), n = 0 → is_zero n

#check is_zero.zmk

theorem zero_is_zero : is_zero 0 :=
begin 
    apply is_zero.zmk 0 (eq.refl 0)
end

/-
Inductively defined proof
-/
inductive is_even : ℕ → Prop
| pf_zero_is_even : (is_even 0)
| pf_n_minus_two_is_even :
    ∀ (n : ℕ), is_even n → is_even (nat.succ (nat.succ n))

open is_even

theorem zero_is_even : is_even 0 := pf_zero_is_even

theorem two_even : is_even 2 :=
begin
end