inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

#check @ImageOf
def f := Nat → Nat
#check @ImageOf f

open ImageOf
def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, imf a => a


inductive Vector (α : Type u) : Nat → Type u
  | nil : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

