-- Notes 10/3/2019

-- example of a polymorphic function: identity function
def identity {α : Type} : α → α 
| x := x

-- explicit type arguments are denoted by ()
-- implicit type arguments are denoted by {}

def id' (α : Type) (a : α) : α := a

#eval id' nat 3
#check (id' nat) -- we can partially evaluate id', making a monomorphic version of this function

def not_predicate {α : Type} : (α → bool) → (α → bool)
| f := λ x, ¬(f x)

def is_even : nat → bool
| 0 := tt
| 1 := ff
| (n' + 2) := is_even n'

def is_odd := not_predicate is_even

#eval is_even 2
#eval is_odd 1


-- Back to our boxed example

inductive boxed ( α : Type )
| box : α → boxed

def unbox {α : Type} : (boxed α) → α
| (boxed.box x) := x

#eval unbox (boxed.box 3)
#eval unbox (boxed.box "hello")
#reduce unbox (boxed.box (boxed.box (boxed.box 3)))

/-
A polymorphic ordered pair example (cartesian product)
-/

inductive mprod (α β : Type)
| pair : α → β → mprod

-- return the first element of our pair
def first {α β : Type} : (mprod α β) → α 
| (mprod.pair x _) := x

-- return the second element of our pair
def second {α β : Type} : (mprod α β) → β 
| (mprod.pair _ y) := y

def ex := mprod.pair 2 3
#check ex

#eval first ex

def p1 : (mprod string nat) := (mprod.pair "cat" 1)

#eval second p1

-- Challenge time!

def swap {α β : Type} : (mprod α β) → (mprod β α)
| (mprod.pair x y) := (mprod.pair y x)

#reduce swap ex