namespace hidden

inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) where
  | intro : a → b → And a b

inductive Or1 (a b c : Prop) where
  | inl : a → Or1 a b c
  | inm : b → Or1 a b c
  | inr : c → Or1 a b c

inductive Exists {α : Type u} (q : α → Prop) : Prop where
  | intro : ∀ (a : α), q a → Exists q

end hidden

#print hidden.False

#print hidden.True

#print hidden.And

#print hidden.Or1
#print Subtype