-- propositions
-- proofs
-- predicates
    -- sets
    -- relations
    -- equality
-- connectives
    -- not
    -- and
    -- or

-- proposition
inductive nifty_was_a_cat : Prop
-- proof
| there_are_pictures_of_nifty
| we_remember_nifty_fondly

inductive pet : Type 
| nifty
| tom
| cheese
| kevin

open pet

inductive was_a_cat : pet → Prop
| nifty_proof : was_a_cat nifty
| tom_proof : was_a_cat tom

open was_a_cat

theorem nifty_cat : was_a_cat nifty := nifty_proof

-- Predicates with single arguments, in essence, define a *set*
-- The elements of this set all satisfy the predicate
-- (elements that do not satisfy the predicate are not members)
-- A kind of "membership test" for being in a set

inductive and'' (α β : Prop) : Prop
| intro : α → β → and''

def nwac_and_cwac : Prop := and'' (was_a_cat nifty) (was_a_cat cheese)

theorem pf : (and'' (was_a_cat nifty) (was_a_cat tom)) := and''.intro (nifty_proof) (tom_proof)

def and''_intro (α β : Prop) : α → β → (and'' α β) := and''.intro

def and''_elim_left {α β : Prop} : (and'' α β) → α
| (and''.intro a b) := a

def and''_elim_right {α β : Prop} : (and'' α β) → β 
| (and''.intro a b) := b

theorem twac : (was_a_cat tom) := (and''_elim_right pf)

-- if you have a data type of one constructor, you can use the "structure" keyword to declare it

inductive and''' (α β : Prop) : Prop 
| intro (left : α) (right : β) : and'''

structure and' (a b : Prop) : Prop := intro :: (left : a) (right : b)