namespace test

class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue (h : p) : Decidable p

def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)

def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t

end test

#eval ite (0 > 1) 1 2
#check ite
#eval dite (0 > 1) (fun h : (0 > 1) => 1) (fun h : ¬ (0 > 1) => 2)
#eval if h : (0 > 1) then 1 else 2
#check dite


#check @instDecidableAnd
#check @instDecidableOr
#check @instDecidableNot


def step (a b x : Nat) : Nat :=
  if (x < a) ∨ (x > b) then 0 else 1

--set_option pp.explicit true
#print step

#eval step 1 3 2



namespace hidden

open Classical

noncomputable scoped
instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩

end hidden

example : (10 < 5) ∨ (1 > 0) := by decide

example : ¬ (True ∧ False) := by decide

theorem gh : 10 * 20 = 200 := by decide

theorem ex : True ∧ (2 = 1 + 1) := by decide

#print ex

#check @of_decide_eq_true
#check @decide

#eval decide (1 > 0)