/-
A reiteration:

When we write some term on paper / in a program, it is understood to represent something in the "real world."

In other words, programs have syntax,
but we give the terms semantics. We
interpret these terms.

What kind of terms will we use to represent lists?
I.e., how do we represent sequences of *things*
using the terms at our disposal?

Some lists
[1, 2, 3]
["hi", "there"]
[tt, ff, tt, tt]
-/

open list -- open the list namespace

/-
Lists have two constructors: nil and cons

Lists are either empty (nil) or they are an element
followed by a one-smaller list.

Compare this to our natural number inductive type,
which had two constructors: zero and succ.

Lean lists are polymorphic—they can contain types of any kind.

-/

def e : list nat := nil -- an empty list e of nats (c.f. generics in rust, java, etc.)

/-
To represent a non-empty list, we need to express each element followed by smaller lists.

Say we wanted to represent [1,2,3].
This would be represented as 1 — [2, 3] = 1 - 2 [3] = 1 - 2 - 3 - nil
Or, (cons 1 (cons 2 (cons 3 nil)))
-/

/-
Let's represent [1].

Think of (cons h t) as "cons head tail"
-/

def l1 : list nat := 
    cons 1 nil

/-
Now, recognize that the second argument of "cons" can be any type of list nat (nil here is the empty nat list)
-/

-- [1, 2]
def l2 : list nat :=
    cons 1 (cons 2 nil)

-- nested list example
-- here is a list of nat-lists
def l3: list (list nat) :=
    (cons (nil) (cons (cons 1 nil) nil))

-- back to one-dimensional lists

def mylist: list string :=
    (cons "I" 
        (cons "love"
            (cons "discrete"
                (cons "math" nil))))

def nested_list : list (list nat) :=
(cons
    (cons 1 (cons 2 nil))
    (
        cons
        (cons 3 (cons 4 nil))
        (
            cons
            (cons 0 (cons 10 nil))
            nil
        )
    ))
    
-- syntactic sugar time!

def l4 : list nat := [1,2,3,4]
-- desugared:
def l4' : list nat := (cons 1 (cons 2 (cons 3 (cons 4 nil))))

-- this feels like a useless function, but who am i?
def prepend : nat → list nat → list nat := cons

-- returns the head of the list
def head' : list nat → nat -- (uses ' so as not to conflict with list.head)
| nil := 0
| (cons h t) := h

#eval head' (prepend 5 [1,2,3])

-- so no head?

def tail' : list nat → list nat
| nil := nil
| (cons h t) := t

#eval tail' [1,2,3]

def last_elem : list nat → nat
| nil := 0
| (cons h nil) := h
| (cons h t) := last_elem t

#eval last_elem  [3,4,5]

def length' : list nat → nat
| nil := 0
| (cons h t) := 1 + (length' t)

#eval length' [1, 2, 33]

-- map: applies a function to every element of a list
def map' : (nat → nat) → list nat → list nat
| _ nil := nil
| f (cons h t) := (cons (f h) (map' f t))

-- Map is a higher-ordered function: a function that takes a function as an argument
#eval map' (λ x, x*x) [1,2,3]