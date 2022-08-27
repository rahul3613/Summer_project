example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n))
        : ∀ n, p n := by
      intro (n : Nat)
      cases n
      . exact hz
      . apply hs


open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero => apply absurd rfl h
  | succ m => rfl

/--/
def f (n : Nat) : Nat := by
  cases n
  . exact 3
  . exact 7

#eval f 9

example : f 0 = 3 := by rfl  -- use rfl if some property comes from a definition.
example : f 5 = 7 := by rfl
-/

def Tuple (α : Type) (n : Nat) :=
  {as : List α // as.length = n}

def f {n : Nat} (t : Tuple α n) : Nat := by
  cases n 
  . exact 3
  . exact 7

def myTuple : Tuple Nat 3 :=
  ⟨[0, 1, 2], rfl⟩

example : f myTuple = 7 := 
  by rfl


inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar1 a b => exact b
  | bar2 c d e => exact e


def silly1 (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b => exact b

def silly2 (x : Foo) : Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b => exact b


example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
    cases m + 3 * k
    exact hz
    apply hs


example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
    generalize m + 3 * k = n
    cases n
    exact hz
    apply hs


example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
    cases Nat.lt_or_ge m n
    case inl hlt => exact h₁ hlt
    case inr hge => exact h₂ hge
  

example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
    have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
    cases h
    case inl hlt => exact h₁ hlt
    case inr hge => exact h₂ hge


#check Nat.sub_self

example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => rw [heq]
               apply Or.inl
               . exact Nat.sub_self n
  | inr hne => apply Or.inr
               . exact hne

#check Decidable.em


theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    calc 
      0 + succ n = succ (0 + n) := by rfl
      _ = succ n := by rw [ih]


theorem zero_add1 (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => 
    calc 
      0 + succ n = succ (0 + n) := by rfl
      _ = succ n := by rw [ih]


example (x : Nat) {y : Nat} (h : y > 0) : (x % y) < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
    have : ¬ (0 < y) ∨ ¬ (y ≤ x) := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
    match this with
    | Or.inl h₁ => exact absurd h h₁
    | Or.inr h₁ =>
      have hgt : y > x := Nat.gt_of_not_le h₁
      rw [←Nat.mod_eq_of_lt hgt] at hgt
      assumption

#eval 6%6

example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl hp => apply Or.inr; exact hp
  | Or.inr hq => apply Or.inl; exact hq


example : s ∧ (q ∧ r) → p ∧ r → q ∧ p := by
  intro ⟨hs, ⟨hq, hr⟩⟩ ⟨hp, hr⟩
  exact ⟨hq, hp⟩


example :
      (fun (x y : Nat × Nat) => x.1 + y.2) =
      (fun (x z : Nat × Nat) => z.2 + x.1) := by
    funext (a, b) (c, d)
    show a + d = d + a
    rw [Nat.add_comm]


example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
    injection h with h'
    injection h' with h''
    rw [h'']


example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

theorem t1 (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

#print t1

example (h : 7 = 4) : False := by
  contradiction