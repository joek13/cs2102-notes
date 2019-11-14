def there_is_no_largest_nat := ¬ ∃ (n : nat), ∀ (k : nat), n > k

inductive friend : Type
| harsh : friend
| joe : friend
| will : friend
| sullivan : friend

inductive taller : friend → friend → Prop
| trans : ∀ (a b c : friend), (taller a b) → (taller b c) → taller a c

open friend
def joe_taller_harsh := taller joe harsh
def harsh_taller_kevin := taller harsh sullivan
def joe_taller_kevin := taller joe sullivan

axiom tallest : ∀ (f : friend), taller will f 

def mtransitive {α : Type} (r : α → α → Prop) : (Prop) := ∀ (a b c : α), r a b → r b c → r a c

example : taller joe harsh → taller harsh sullivan → taller joe sullivan :=
begin
    apply taller.trans,
end

def myreverse {α : Type} : list α → list α
| list.nil := []
| (list.cons a t) := list.append (myreverse t) [a]

#eval myreverse [1,2,3]