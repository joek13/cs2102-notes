-- Notes 9-19-2019

/-
Abstract data type - a data type accompanied by functions that operate on values of that type

Propositions are true or false.
-/

namespace mylogic

inductive kevin_sullivan_is_daddy : Type
| ttt
| fff
| idk

open kevin_sullivan_is_daddy

def daddy_and : kevin_sullivan_is_daddy → kevin_sullivan_is_daddy → kevin_sullivan_is_daddy
    | fff _ := fff
    | _ fff := fff
    | ttt ttt := ttt
    | ttt idk := idk
    | idk ttt := idk
    | idk idk := idk

/-
Terms / representationts              Values

"joe"                            →    a person named "joe"
Flight 66                        →    some airplane in the world
3/011/III/succ(succ(succ(zero))) →    some natural number three
-/

/-
In defining the natural numbers, we want to define a datatype
whose values are these terms.
-/


end mylogic

namespace mynat

inductive knat : Type 
| zero : knat
| succ : knat → knat

open knat

def one := succ zero
def two := succ one
def three := succ two
def four := succ three

#reduce four -- a beautifully simple counting system

def increment : knat → knat :=
    λ (x : knat),
        succ x

def decrement : knat → knat
    | zero := zero
    | (succ x) := x -- need parentheses so it is interpreted as one argument
-- unification algorithm (for pattern matching)

def is_zero : knat → bool
    | zero := tt
    | _ := ff

def keq : knat → knat → bool
    | zero zero := tt
    | zero (succ _) := ff
    | (succ _) zero := ff
    | (succ x) (succ y) := keq x y -- lean guarantees that recursion will terminate

#eval keq three three
3
end mynat