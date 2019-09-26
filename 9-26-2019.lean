/- Notes 9/26/2019

First, let's recall some facts from the last lecture:
- List are polymorphic (they abstract over generic types—they've been parameterized)
- Lists have two constructors (nil, and cons h t)
- cons h t takes a head element and a tail list; nesting cons expressions lets us make lists of any length

[1,2,3,4,5] = (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil)))))

Let's warm up that cache, says Kevin Sullivan.

Recall an instance of "recursive thinking:"
- we consider the inductive definition of some datatype when we're planning operations on that type
-/

open list

def countdown : nat → list nat 
| 0 := [0]
| (nat.succ x) := (cons (nat.succ x) (countdown (x)))

def countdown' : nat → list nat
| 0 := [0]
| n := (cons n (countdown (n-1)))

-- countdown 10 = (cons 10 (countdown 9))
#eval countdown 5
#eval countdown' 6

def lt : nat → nat → bool
| a b := a < b

def fib : nat → nat
| 0 := 0
| 1 := 1
| (nat.succ (nat.succ n)) := fib n + fib(n+1)

def fib_invalid : nat → nat
| 0 := 0
| 1 := 1
| n := fib(n-1) + fib (n-2)

#eval fib_invalid 3

-- Higher-ordered function: a function that takes a function as an argument

-- Read this definition super carefully!
def kevinmap : (nat → nat) → list nat → list nat
| f nil := nil
| f (cons h t) := (cons (f h) (kevinmap f t))

#eval kevinmap (λ x, x*2) [1,2,3]

-- (reduce + 0 [1,2,3]) - 


-- reduce applies the same function to each successive element
def mreduce : (nat → nat → nat) → nat → list nat → nat 
| f ident nil := ident
| f ident (cons h t) := (f h (mreduce f ident t))

#eval mreduce (λ a b, a+b) 0 [1,2,3]
#eval mreduce (λ a b, a*b) 1 [1,2,3,4]