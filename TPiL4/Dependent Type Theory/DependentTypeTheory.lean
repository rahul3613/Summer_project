def cons (α : Type) (a : α) (as : List α) : List α := List.cons a as

#check cons
#check cons Bool
#check cons Nat

#check @List
#check @List.cons
#check @List.nil
#check @List.length
#check @List.append

universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a := ⟨a, b⟩
 #print f

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a := Sigma.mk a b
#print g

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5

def h2 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h2 5