
-- Basic navigation and rewriting
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    skip
    rw [Nat.mul_comm]


example : (fun x : Nat => 0 + x) = (fun x => x) := by 
  rw [Nat.zero_add]

example : (fun x : Nat => 0 + x) = (fun x => x) := by 
  conv =>
  lhs
  intro x
  rw [Nat.zero_add]

example : (fun x : Nat => 0 + x) = (fun x => x) := by
  funext x
  rw [Nat.zero_add]

example : (fun x : Nat => 0 + x) = (fun x => x) := by
  simp


-- Pattern Matching

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c => rw [Nat.mul_comm]

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
  pattern b * c
  rw [Nat.mul_comm]

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in _ * c => rw [Nat.mul_comm]


-- Structuring conversion tactics

example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    . rw [Nat.zero_add]
    . rw [Nat.mul_comm]


-- Other tactics inside conversion mode

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
      args
      . skip
      . rw [Nat.mul_comm]
  
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
      arg 2
      . rw [Nat.mul_comm]


def f (x : Nat) := if x > 0 then x + 1 else x + 2

example (g : Nat → Nat) (h₁ : g x = x + 1) (h₂ : x > 0) : g x = f x := by
  conv =>
    rhs
      simp [f, h₂]
      exact h₁


example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . skip
    . tactic => exact h₂


example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . skip
    . apply h₂