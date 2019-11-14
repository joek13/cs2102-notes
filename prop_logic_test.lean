import .prop_logic
open prop_logic
open prop_logic.var
open prop_logic.unOp
open prop_logic.binOp
open prop_logic.pExp


def varX := mkVar 0
def varY := mkVar 1
def varZ := mkVar 2
def varW := mkVar 3

def X := varExp varX
def Y := varExp varY
def Z := varExp varZ
def W := varExp varW

-- Notes on operator precedence
def mystery :=  ¬ (X ∧ Y) ∨ (¬ X ∧ ¬ Y)
#check mystery
-- Does the above expression represent ¬((X ∧ Y) ∨ (¬ X ∧ ¬ Y))
-- ... or does it represent (¬ (X ∧ Y)) ∨ (¬ X ∧ ¬ Y)
#reduce mystery

-- Since not has a higher precedence (or "binding power") than or

def pxor := (X ∧ ¬Y) ∨ (¬X ∧ Y)

def pXor : pExp → pExp → pExp 
| a b := (a ∧ ¬b) ∨ (¬a ∧ b)

#reduce pXor X Y

notation a ⊕ b := pXor a b

-- our variable interpretation function simply takes us from variable to boolean value
def allFalse : var → bool
| _ := ff
def allTrue : var → bool
| _ := tt

def interp : (var → bool)
| (mkVar 0) := tt -- X
| (mkVar 1) := ff -- Y
| (mkVar 2) := tt -- z
| (mkVar 3) := ff -- W
| _ := ff

#eval allFalse varX
#eval allTrue varX
#eval interp varX
#eval interp varY

#eval pEval pTrue allFalse -- still true, as pTrue is a literal—not a variable

#eval pEval (X ⊕ Y) interp

def max' (a b : nat) : nat := if a > b then a else b

def var_list : pExp → list nat
| (pExp.litExp _) := list.nil
| (pExp.varExp (mkVar n)) := [n]
| (pExp.unOpExp o e) := var_list e
| (pExp.binOpExp o e1 e2) := list.append (var_list e1) (var_list e2) 

def pred_any {α : Type} : (α → bool) → list α → bool 
| f list.nil := ff
| f (list.cons a t) := bor (f a) (pred_any f t)

def unique_list : list nat → list nat 
| list.nil := list.nil
| (list.cons a t) := if (pred_any (λ e, e=a) t) then unique_list t else list.cons a (unique_list t)

def len {α : Type} : list α → nat
| list.nil := 0
| (list.cons a t) := 1 + len t

def count_variables : pExp → nat :=
    λ exp, len (unique_list (var_list exp))

#eval count_variables (pAnd (pXor X Y) (pNot Z))