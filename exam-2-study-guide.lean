/- *** I. FORMAL LANGUAGES *** -/

/- 
Using our implementation of the syntax and semantics of propositional logic, know how to implement the syntax and semantics of simple arithmetic expressions, with natural number literal expressions, natural number-valued variable expressions, and natural number unary and binary operators.
-/

/- *** II. PREDICATE LOGIC *** -/

/-
Be able to write *formal* propositions and predicates n predicate logic to "formalize" natural language statements of propositions and predicates i. Such propositions and predicates can involve both universal and existential quantifiers, alone or in combination: e.g., forall x, exists y, not P x y. 
-/

/-
Be able to *naturalize* formal propositions and predicates by translating formal versions into natural language. You will have to go beyond just "saying words for symbols." Rather, you'll need to find "natural" ways to say what propositions mean. For example, \all x, exists y, P x y should not be translated as "for all x there exists some y such that P x y." It will be necessary to say something like "every x P some y."
-/

inductive dog : Type
variable fido : dog

inductive has_legs {α : Type} : α → Prop

/- All dogs have legs -/
axiom dogs_have_legs : ∀ (d : dog), has_legs d

/- Fido has legs -/
theorem fido_has_legs : has_legs fido := begin
    apply dogs_have_legs,
end

inductive person : Type
inductive likes : person → person → Prop

axiom everyone_likes_self : ∀ p : person, likes p p
axiom everyone_likes_someone : ∀ p : person, ∃ q : person, likes p q
axiom someone_likes_everyone : ∃ p: person, ∀ q : person, likes p q
def nobody_likes_someone : Prop := ∃ p : person, ∀ q : person, ¬likes q p

variable bill : person
example : ¬nobody_likes_someone := begin
    apply not.intro,
    unfold nobody_likes_someone,
    assume h,
    apply exists.elim h,
    assume a,
    assume ha,
    have a_dislikes_self : ¬likes a a := (ha a),
    have a_likes_self : likes a a := everyone_likes_self a,
    contradiction
end

/- *** II. PROOFS *** -/

/- Give both natural language and formal proofs of propositions, including proofs for "inductively defined families of propositions" (such as we did for is_even). We will not ask you to prove propositions with negation or existential quantification except perhaps for extra credit, as we have not covered them yet. -/

inductive id_nat : nat → nat → Prop
| mk : ∀ (a b : nat), a = b → id_nat a b

def transitive' {α : Type} (r : α → α → Prop) : Prop :=
    ∀ (a b c : α), r a b → r b c → r a c

theorem id_nat_transitive : transitive' id_nat :=
begin
    unfold transitive',
    assume a b c,
    assume hab,
    assume hbc,
    induction hab with a b ab,
    induction hbc with b c bc,
    apply id_nat.mk,
    exact eq.trans ab bc,
end

theorem id_nat_transitive' : transitive' id_nat :=
    λ (a b c : nat),
        λ (hab : id_nat a b) (hbc : id_nat b c),
            sorry
            

/- EXTRA CREDIT -/

/-
Show that you've gone beyond what we've covered in class, e.g., to an understanding of negation in the constructive logic of the Lean proof assistant.

More details to come.
-/
theorem test (P: Prop) : ¬ (P ∧ ¬P) := begin
    apply not.intro,
    assume PnP,
    have hp : P, from (and.elim_left PnP),
    have hnp : ¬P, from (and.elim_right PnP),
    contradiction
end

theorem is_2 : ∃ (n : nat), n = 2 := exists.intro 2 (eq.refl 2)
