inductive Vector (α : Type u) : Nat → Type u where
  | nil : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)


namespace hidden

inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a

end hidden

universe u v
#check (@Eq.rec : {α : Sort u} → {a : α} → {motive : (x : α) → a = x → Sort v}
        → motive a rfl → {b : α} → (h : a = b) → motive b h)

theorem symm {α : Type u} {a b : α} (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl