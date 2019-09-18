/-
Kinds of terms that we've encountered thus far:
- literal terms, including lambda abstractions
- identifier terms
- application expressions 

Terms are syntactic expressions that represent values.
How do we get from a term to its value? Evaluation.

(This should all be familiar and already be in the notes)

In a language like Lean, all values have types.
-/

/-
Lean's standard library provides implementations with a set of built-in types like nat, bool, or string.
-/

#check nat -- ℕ is of type Type

/-
How might we define types like bool, etc. without a standard library?
-/

namespace ex1

-- In general, the constructors of some datatype are functions that take arguments.
-- But we don't necessarily *need* to take arguments.
inductive mybool : Type
| ttt : mybool -- here, ttt and fff are constructors of unique values. In more precise terms, constructors are *injective.*
| fff : mybool -- this is Lean's concept of an enumerated type (enum in java, rust, etc., etc.)
-- note that this is an exhaustive list: mybool is defined as either being ttt or fff
-- injective functions ensure that each distinct x produces a distinct y.

open mybool
def neg_mybool : mybool → mybool :=
    λ (b : mybool),
        match b with
            | ttt := fff
            | fff := ttt
        end

def neg_mybool'' : mybool → mybool
    | ttt := fff
    | fff := ttt

end ex1

namespace foo

def x := 5 -- foo.x

namespace bar

def x := 6 -- foo.bar.x

#eval x -- refers to foo.bar.x

end bar

#eval x -- refers to foo.x

end foo

#eval foo.x
#eval foo.bar.x

open foo
#eval x

/-
Referential transparency - we can replace any kind of reference with its value without changing the functionality

Pure functions have referential transparency—we can always replace (+ 3 4) with 7.#check
If our + function somehow was non-pure and wasn't guaranteed to return 7 when (+ 3 4) is called, we lose referential transparency.
-/

inductive day : Type 
| sunday : day
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day

open day

def myrepr : day → string 
    | sunday := "sunday"
    | monday := "monday"
    | tuesday := "tuesday"
    | wednesday := "wednesday"
    | thursday := "thursday"
    | friday := "friday"
    | saturday := "saturday"

def next_day : day → day
    | sunday := monday
    | monday := tuesday
    | tuesday := wednesday
    | wednesday := thursday
    | thursday := friday
    | friday := saturday
    | saturday := sunday

def is_weekday : day → bool
| sunday := ff
| saturday := ff
| _ := tt

inductive mynat 
| zero : mynat
| succ : mynat → mynat -- give me the succ, kevin sullivan.
-- reductive types

#reduce (mynat.succ (mynat.succ mynat.zero))