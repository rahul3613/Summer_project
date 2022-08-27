variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

#check h 
#check h 0

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

notation "‹" p "›" => show p by assumption

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun h1 : f 0 ≥ f 1 =>
  fun h2 : f 1 ≥ f 2 =>
  have (h3 : f 0 ≥ f 2) := Nat.le_trans (h2) (h1)
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this h3
