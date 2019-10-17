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