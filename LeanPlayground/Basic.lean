def hello := "world"

def m := 1
def m_2 : Int := 2

def b := true

#check m_2
#eval b ∨ false
#check b || false
#check b && false
#eval (b ∧ false)
#check m+1 * 2
#eval m-10
#eval m_2-10


#check Nat → Nat
#check (0, 1).1
#eval Nat.succ 2

def α: Type := Nat
#check Prod (Nat → Nat)
#check (Prod Nat Bool)

def t : Prop := true
def Bool_1 : Type 0 := Bool
def F : Type 1 := Nat -> Type
def F_2 : Type 2 := Bool -> Type 1

def D: Type := Prod Nat Bool
def e₁: D := (2, true)

#check D

#eval e₁.2

#check Type
#check Type 0

#check List
universe u
def F₃ (a: Type u) : Type u := Prod a a
