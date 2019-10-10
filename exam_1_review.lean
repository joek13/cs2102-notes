/-
Give examples of terms of various types, including basic data types and function types.
To answer the function-type-related questions, you really must know how to write lambda expressions.
-/

/-
Types of terms:

- literal terms (e.g. 5, tt, "hello")
- identifier terms (e.g. x)
- application expressions
-/

/- Writing lambda expressions:
-/

def add_five : nat → nat := λ (n : nat), n + 5

def sum_nats : nat → nat → nat := λ (a : nat), λ (b : nat), a + b
def sum_nats' : nat → nat → nat := λ (a b : nat), a+b -- functionally equivalent, as lean supports partial evaluation of functions
def sum_nats'' (a b : nat) : nat := a+b -- "c-style"

-- partial evaluation example
def add_six : nat → nat := sum_nats 6
def add_six' : nat → nat := λ (n : nat), sum_nats 6 n

#check add_six
#check add_six'

#eval add_six 3

-- Be able to produce recursive function definitions (in Lean) for simple arithmetic functions.

inductive jnat 
| zero : jnat
| succ : jnat → jnat

open jnat

def one := succ zero
def two := succ one
def three := succ two
def four := succ three
def five := succ four
def six := succ five
def seven := succ six
def eight := succ seven
def nine := succ eight
def ten := succ nine

-- helper method so we don't have to count succ's
def convert : jnat → nat
| zero := 0
| (succ n') := 1 + convert n'

#eval convert ten

def increment : jnat → jnat := succ
#reduce convert (increment one)

def decrement : jnat → jnat
| zero := zero
| (succ n') := n'

#reduce convert (decrement one)

def add : jnat → jnat → jnat
| zero zero := zero
| zero b := b
| (succ a) b := add a (succ b)

#eval convert (add five ten)

def subtract : jnat → jnat → jnat
| zero _ := zero
| a zero := a
| (succ a') (succ b') := subtract a' b'

#eval convert (subtract ten three)

def multiply : jnat → jnat → jnat
| zero _ := zero
| _ zero := zero
| a (succ b') := (add a (multiply a b'))

#eval convert (multiply two one)

-- remember: factorial of zero is one!

def factorial : jnat → jnat
| zero := succ zero
| (succ n') := (multiply (succ n') (factorial n'))

#eval convert (factorial three)

def exp : jnat → jnat → jnat
| a zero := succ zero
| a (succ b') := (multiply a (exp a b'))

#eval convert (exp ten two)