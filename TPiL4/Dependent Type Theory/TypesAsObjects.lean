#check Nat
#check Bool

#check Nat → Bool
#check Nat × Bool
#check Nat → Nat

#check Nat × Nat → Nat
#check Nat → Nat → Nat

/- def α : Type := Nat
#check α

def β : Type := Bool
#check β

def F : Type → Type := List
#check F α

def G : Type → Type → Type := Prod
#check G α 

#check G α Nat
-/

/-
def α : Type := Nat
def β : Type := Bool

#check Prod α β
#check α × β

#check Prod Nat Nat
#check Nat × Nat
#check (1, 2.0, true)
-/

def α : Type := Nat
#check List α 
#check List Nat

#check Type
#check Type 0

#check Type 1
#check Type 2

#check List
#check Prod

/-
universe u
def F (α : Type u) : Type u := Prod α α
#check F
-/

def F.{u} (α : Type u) : Type u := Prod α α
#check F