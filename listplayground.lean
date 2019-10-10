inductive jlist (α : Type) : Type
| nil : jlist
| cons : α → jlist → jlist
open jlist 

def nat_list : jlist nat := (cons 1 (cons 2 (cons 3 (nil nat))))

def count {α : Type} : jlist α → nat
| (nil α) := 0
| (cons h t) := 1 + (count t)

#eval count nat_list

def append {α : Type} : jlist α → α → jlist α
| (nil α) e := (cons e (nil α))
| (cons h t) e := (cons h (append t e))

#reduce nat_list
#reduce append nat_list 4

def map {α : Type} {β : Type} : (α → β) → jlist α → jlist β
| f (nil α) := (nil β)
| f (cons h t) := (cons (f h) (map f t))

def bool_not : bool → bool := λ (b : bool), ¬ b

def bool_list := (cons tt (cons ff (nil bool)))

#reduce (map bool_not bool_list)

def fold {α : Type} {β : Type} : (α → β → β) → β → jlist α → β
| f i (nil α) := i
| f i (cons h t) := (f h (fold f i t))

def jsum : jlist nat → nat := λ (l : jlist nat), fold (λ (a b : nat), a + b) 0 l
#eval jsum nat_list

def filter {α : Type} : (α → bool) → jlist α → jlist α
| f (nil α) := (nil α)
| f (cons h t) := 
    if f h
        then (cons h (filter f t))
        else (filter f t)

def pred : nat → bool := λ (n : nat), n >= 3

def nat_list_2 : jlist nat := (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 (cons 6 (nil nat)))))))
#reduce nat_list_2
#reduce filter pred nat_list_2

def concat { α : Type } : jlist α → jlist α → jlist α
| (nil α) b := b
| a (nil α) := a
| (cons h t) b := (cons h (concat t b))

#reduce concat (cons 1 (cons 2 (cons 3 (nil nat)))) (cons 4 (cons 5 (cons 9 (nil nat))))

inductive mprod (α β : Type)
| pair : α → β → mprod

open mprod

def first { α β : Type} : mprod α β → α
| (pair a _) := a

def second { α β : Type} : mprod α β → β
| (pair _ b) := b

-- zips two jlists into a single jlist of prods
def zip {α β : Type} : jlist α → jlist β → jlist (mprod α β)
| (nil α) _ := (nil (mprod α β))
| _ (nil β) := (nil (mprod α β))
| (cons a t1) (cons b t2) := (cons (pair a b) (zip t1 t2))

def nums := (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 (nil nat))))))
def bools := (cons tt (cons tt (cons tt (cons ff (cons ff (nil bool))))))

def zipped := zip nums bools
#reduce zipped

def trim { α : Type } : jlist α → nat → jlist α
| (nil α) _ := (nil α)
| l 0 := l
| (cons h t) (nat.succ n') := (trim t n')

-- trims the start of a list using a predicate
def trim_while {α : Type} : (α → bool) → jlist α → jlist α
| _ (nil α) := (nil α)
| f (cons h t) := if f h then (trim_while f t) else (cons h t)

def three_to_five := trim nums 2
#reduce three_to_five

def so_many_threes := (cons 3 (cons 3 (cons 3 (cons 3 (cons 3 (cons 3 (cons 4 (cons 3 (cons 5 (nil nat))))))))))
#reduce trim_while (λ (n : nat), n=3) so_many_threes

def flatten { α : Type } : jlist (jlist α) → jlist α
| (nil jlist) := (nil α)
| (cons h t) := (concat h (flatten t))

def flatten' { α : Type } : jlist (jlist α) → jlist α := fold concat (nil α)
-- we can define flatten in terms of successive concatenations

def convert { α : Type } : list α → jlist α 
| (list.nil) := (jlist.nil α)
| (list.cons h t) := (jlist.cons h (convert t))

def bconvert { α : Type} : jlist α → list α
| (jlist.nil α) := list.nil
| (jlist.cons h t) := (list.cons h (bconvert t))

def nested_list_1 := convert [1,2,3,4,5]
def nested_list_2 := convert [6,7,8,9,10]
def nested_list_3 := convert [11,12,13,14,15]
def big_boy := convert [nested_list_1, nested_list_2, nested_list_3]

#reduce bconvert (map bconvert big_boy)
#eval bconvert (flatten big_boy)
#eval bconvert (flatten' big_boy)

def all { α : Type } : (α → bool) → (jlist α) → bool :=
    λ (f : (α → bool)) (l : jlist α),
        (fold band tt (map f l))

def evens := convert [2,4,6,8]
def odds := convert [1,3,5,7]
def evens_almost := convert [2,4,6,8,9]

def is_even : nat → bool
| nat.zero := tt
| (nat.succ nat.zero) := ff
| (nat.succ (nat.succ n')) := is_even n'

#eval all is_even evens_almost

def any { α : Type } (f : α → bool) (l : jlist α) : bool := (fold bor ff (map f l))

#eval any is_even odds