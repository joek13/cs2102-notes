namespace prop_logic 

-- syntax

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

def pNot := pExp.unOpExp unOp.notOp -- pExp → pExp
#check pNot
def pAnd := pExp.binOpExp binOp.andOp -- partial evlaution of binOpExp - pExp → pExp → pExp
#check pAnd
def pOr := pExp.binOpExp binOp.orOp -- pExp → pExp → pExp
#check pOr

notation e1 ∧ e2 := pAnd e1 e2 -- "Mr. or Mrs. Lean"
notation e1 ∨ e2 := pOr e1 e2
notation ¬ e := pNot e

-- If syntax represents the rules/structure of our formal language, what are the semantics?
/-
They define the meaning of syntactically legal/valid expressions
-/

-- semantics!

-- we interpret notOp as representing boolean not
def interpUnOp : unOp → (bool → bool)
| notOp := bnot

-- likewise, we interpret andOp and orOp as representing boolean and and or, respectively
def interpBinOp : binOp → (bool → bool → bool)
| binOp.andOp := band
| binOp.orOp := bor

def pEval : pExp → (var → bool) → bool
| (pExp.litExp b) i := b -- literals need not be interpreted
| (pExp.varExp v) i := i v -- just get the current interpretation's value for the var
| (pExp.unOpExp o e) i := (interpUnOp o) (pEval e i) -- apply the unary operation to this value
| (pExp.binOpExp o e1 e2) i := (interpBinOp o) (pEval e1 i) (pEval e2 i) -- apply the binary operation to the values

end prop_logic

