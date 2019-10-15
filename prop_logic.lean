namespace prop_logic 
inductive var : Type
| mkVar : ℕ → var

inductive unOp : Type
| notOp

inductive binOp
| andOp
| orOp

inductive pExp
| litExp : bool → pExp
| varExp : var → pExp -- "variable expression"—like a "box with a variable in it"
| unOpExp : unOp → pExp → pExp
| binOpExp : binOp → pExp → pExp → pExp

def pTrue := pExp.litExp tt
def pFalse := pExp.litExp ff

def pNot := pExp.unOpExp unOp.notOp
def pAnd := pExp.binOpExp binOp.andOp
def pOr := pExp.binOpExp binOp.orOp

notation e1 ∧ e2 := pAnd e1 e2
notation e1 ∨ e2 := pOr e1 e2
notation ¬ e := pNot e

def interpUnOp : unOp → (bool → bool)
| notOp := bnot

def interpBinOp : binOp → (bool → bool → bool)
| binOp.andOp := band
| binOp.orOp := bor

def pEval : pExp → (var → bool) → bool
| (pExp.litExp b) i := b
| (pExp.varExp v) i := i v
| (pExp.unOpExp o e) i := (interpUnOp o) (pEval e i) 
| (pExp.binOpExp o e1 e2) i := (interpBinOp o) (pEval e1 i) (pEval e2 i)

end prop_logic

