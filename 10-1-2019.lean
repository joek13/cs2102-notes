-- Notes 10/1/2019

/-
Let's look at our "roadmap:"
    - literal terms
        - values (nat, string, bool, etc.)
        - lambda expressions
            - represent "total functions" (has values for every possible input in domain)
        - type names
            - first-class type system means types themselves are terms
            - allows for generalization over types
                - (list nat) type can be imagined as a function from Type → Type
    - identifier terms
    - function application
-/

-- Notes on polymorphism

-- nat specific box

inductive boxed_nat
| box : nat → boxed_nat

def unbox_nat : boxed_nat → nat
| (boxed_nat.box x) := x


-- "Box" type that generalizes over some type α
inductive boxed (T : Type) : Type
| box : T → boxed

#check boxed -- boxed is a function which "takes" in one type and returns another type

open boxed

def test : boxed nat := box 2

#check test -- "boxed ℕ"


-- polymorphic function to unbox any type
-- note that we have to use the "c-style" syntax here, as we need to refer to the name T in the function's type definition
def unbox (T : Type) : (boxed T) → T
| (box x) := x

-- I don't think it's possible to express this using multiple lambdas

#eval unbox nat test -- "nat" provides value for type argument T

def mybox := box 23 -- boxed ℕ
def inception_box := box mybox -- boxed (boxed ℕ)

#check inception_box
#check unbox _ inception_box -- we can infer the type here, so why even bother?

-- when we use brackets, the type-checker infers a value for T "invisibly"
def smart_unbox {T: Type} : (boxed T) → T
| (box x) := x

#check smart_unbox inception_box

-- Note on import statmeents:
-- import .boxed -- imports local file boxed.lean
-- we can now execute tests on our boxed datatypes