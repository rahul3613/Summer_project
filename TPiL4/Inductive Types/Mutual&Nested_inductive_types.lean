mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)
  
  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end


mutual
  inductive Tree (α : Type u) where
    | node : α → TreeList α → Tree α

  inductive TreeList (α : Type u) where
    | nil : TreeList α
    | cons : Tree α → TreeList α → TreeList α
end


inductive Tree1 (α : Type u) where
  | mk : α → List (Tree1 α) → Tree1 α