/-
1. Give examples of terms of various types, including basic data types and function types.
To answer the function-type-related questions, you really must know how to write lambda expressions.
-/

/-
Term types:
- literal terms (e.g. 3, tt, "hello")
- identifier terms (e.g. x)
- application expressions (e.g. f x)
-/

/- Lambda expressions -/
def sum_nats := λ (a : nat), λ (b : nat), a+b
def sum_nats' := λ (a b : nat), a+b

/-
2. Be able to produce recursive function definitions (in Lean) for simple arithmetic functions. 
-/

open nat
def add : nat → nat → nat
| a zero := a
| a (nat.succ b') := (add (nat.succ a) b')

def sub : nat → nat → nat
| zero a := zero -- underflow case: return zero
| a zero := a
| (nat.succ a') (nat.succ b') := (sub a' b')

def mult : nat → nat → nat
| a zero := zero
| a (nat.succ b') := (add a (mult a b'))

def factorial : nat → nat
| zero := (succ zero) -- 0! = 1
| (succ n') := (mult (succ n') (factorial n'))

/-
3. Understand key tradeoffs when defining functions using mathematical logic, and using imperative programming languages, respectively.
-/

/-
Mathematical logic allows us to be entirely sure that our functions are up to mathematical specification—in a language like lean, specification is a significant part of the syntax.
As a result, however, we can lose performance. Recursive definitions sometimes are unsuitable for practical applications.

On the other hand, imperitive programming languages usually allow us to harness our machine's performance much more effectively, but unforeseen bugs can cause
their outputs to diverge from specification.
-/

/-
4. Understand key shortcomings of natural languages for expressing mathematical (including specification and implementation) concepts.
-/

/-
Natural language, while convenient—and "natural"—for speaking, is ambiguous, inconsistent, and imprecise.

If someone says "your program should subtract natural numbers, returning a natural number," it's not clear what
your program should do if subtraction leads to a negative (non-natural) number. In this way, natural language
leads to an ambiguity in our program's specification.

The same can happen for a procedure—the "implementation." Say that someone wants to know how to make a PB&J Sandwich, and I give
them the following procedure:

1. Get a piece of bread.
2. Spread peanut butter on the bread.
3. Get another piece of bread.
4. Spread jelly on the bread.
5. Put the pieces together.

There are a number of places that leave room for inconsistencies/ambiguous instructions. The "executor" might not realize a knife
is necessary for spreading the various spreads, etc., etc.

Formal languages (such as mathematical logic) have clearly defined syntactical rules, which allow us to verify them objectively.
In other words, specifications writtern in terms of formal languages are checkable, and implementations written in formal languages are unambiguous.
Some formal languages:
- predicate logic
- python
-/

/-
5. Understand precisely what it means for a program to be correct with respect to (or "equivalent" to) a specification written in math logic.
-/

/-
A program, P'(x) meets some specification P(x) if and only if P'(x)=P(x) ∀ x ∈ D
-/

/-
6. Know by heart the truth tables for all of the Boolean functions, both unary and binary, that we have discussed.
-/

/- Unary functions 

IDENTITY: | NOT:    | TRUE:   | FALSE:
          |         |         |
tt → tt   | tt → ff | tt → tt | tt → ff
ff → ff   | ff → tt | ff → tt | ff → ff

-/

def identity : bool → bool
| tt := tt
| ff := ff

def not' : bool → bool
| tt := ff
| ff := tt

def always_true : bool → bool
| tt := tt
| ff := tt

def always_false : bool → bool
| tt := ff
| ff := ff

/- Binary functions (of interest)

AND:
   | tt | ff
---+----+---
tt | tt | ff
ff | ff | ff
-/

def and' : bool → bool → bool
| tt tt := tt
| _ _ := ff

/-
OR:
   | tt | ff
---+----+---
tt | tt | tt
ff | tt | ff
-/

def or' : bool → bool → bool
| tt tt := tt
| tt ff := tt
| ff tt := tt
| ff ff := ff

/-
XOR:
   | tt | ff
---+----+---
tt | ff | tt
ff | tt | ff
-/

def xor' : bool → bool → bool
| tt ff := tt
| ff tt := tt
| ff ff := ff
| tt tt := ff

/-
NOR:
   | tt | ff
---+----+---
tt | ff | ff
ff | ff | tt
-/

def nor' : bool → bool → bool
| ff ff := tt
| _ _ := ff

/-
7. Know how lists ("sequences") are inductively defined and be able to define recursive functions that operate on lists.
-/

inductive jlist (α : Type)
| nil : jlist
| cons : α → jlist → jlist

open jlist

def map {α β : Type } : (α → β) → jlist α → jlist β
| f (nil α) := (nil β)
| f (cons h t) := cons (f h) (map f t)

def reduce {α β : Type} : (α → β → β) → β → jlist α → β
| f i (nil α) := i
| f i (cons h t) := (f h (reduce f i t))

def one_two_three := (cons 1 (cons 2 (cons 3 (nil nat))))

#eval reduce sum_nats 0 one_two_three
#eval reduce mult 1 one_two_three

/-
8. Know how to define polymorphic functions that work with values of type (list alpha),
where alpha is a type parameter. Understand implicit arguments and how to use them in Lean function definitions.
-/

/- (see definitions of map, reduce for jlist α) -/

-- explicit type parameter: must be called with type argument
def length (α : Type) : jlist α → nat
| (nil α) := 0
| (cons h t) := (succ (length t))

-- implicit type parameter: lean infers a type argument invisibly
def length' {α : Type} : jlist α → nat
| (nil α) := 0
| (cons h t) := (succ (length' t))

#eval length nat one_two_three
#eval length _ one_two_three
#eval length' one_two_three

/-
9. Know how to define simple enumerated types in Lean and functions that operate on values of such types.
The "day" type that we covered is an example of such a type.
-/

inductive day
| sunday
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday

def is_weekend : day → bool
| day.sunday := tt
| day.saturday := tt
| _ := ff

def is_weekday : day → bool := λ (d : day), ¬(is_weekend d)

/-
10. Understand the higher-order "map" and "reduce" functions that we've studied.
The key characteristic of higher-order functions is that they take function arguments, or return functions as results, or both.
Be able to implement and use map and reduce functions.
-/

/-
Map applies a function to every element in some listish type, returning a new list of those elements.
Reduce applies a function to each element in some listish type successively, returning a single value computed from each element.
-/

/-
11. Understand how to specify and work with "product" types.
The "prod" type we defined is an example of a type whose values are ordered *pairs* of values of other specified types.
-/

inductive mprod (α β : Type)
| pair : α → β → mprod

def first {α β : Type} : mprod α β → α
| (mprod.pair a _) := a

def second {α β : Type} : mprod α β → β 
| (mprod.pair _ b) := b

def swap {α β : Type} : mprod α β → mprod β α
| (mprod.pair a b) := (mprod.pair b a)

/-
12. Understand the combinatorics of binary values. E.g., there are 2^n possible values of a sequence of n binary variables.
-/

/-
There are 2^n sequence of n binary variables, or 2^n possible values of a n-bit number.

When we consider functions that have input and output, there are (2^m)^(2^n) functions with n-bit inputs and m-bit outputs.

Put differently, if a function takes n booleans in and returns m booleans out, there are (2^m)^(2^n) possible unique mappings.
-/