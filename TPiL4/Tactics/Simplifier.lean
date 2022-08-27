theorem t1 (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : (x + 0) * (0 + y * 1 + z * 0) = x * y :=
        by simp

#print t1


theorem t2 (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
        simp;
        assumption

#print t2

#check Eq.mpr

open List

theorem t3 (xs : List Nat) : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
        simp
#print t3

variable (xs : List Nat)
#check xs ++ [1, 2, 3]
variable (x := xs.length)
#check x


example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
 simp [Nat.add_comm]

example (a b c : Nat) : a + b + c = a + c + b := by
        simp only [Nat.add_left_comm, Nat.add_comm]


example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
        simp at h
        assumption


attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

#check Nat.add_left_comm
#check Nat.add_comm


example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * x * w)) : p (x * w * z + y * x) := by
        simp at *
        assumption


theorem t4 (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p  (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
        simp at * <;> constructor <;> assumption

#print t4


theorem t5 (w x y z : Nat) (p : Nat → Prop)
        : x * y + z * w * x = x * w * z + y * x := by
        simp
#print t5

/-
example (w x y z : Nat) (p : Nat → Prop)
        : x * y + z * w * x = x * w * z + y * x :=
        calc
                x * y + z * w * x = (z * w * x) + (x * y) := by rw [Nat.add_comm]
                _ = (z * w * x) + (y * x) := by rw [Nat.mul_assoc x]
                _ = ((w * z) * x) + (y * x) := by rw [Nat.mul_comm z]
                _ = (x * (w * z)) + (y * x) := by rw [Nat.mul_comm]
                _ = (x * w * z) + (y * x) := by rw [Nat.mul_assoc]
-/

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
        simp at h
        simp
        assumption

def f (m n : Nat) : Nat := m + n + m

theorem t6 {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
        simp [←h', f]

#print t6

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
        simp [h₁, h₂]

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
        simp [*]

example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
        simp [h₁, h₂]

theorem t7 (p q : Prop) (hp : p) : p ∧ q ↔ q := by
        simp [hp]

#print t7

example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
        apply Iff.intro
        . intro hpq
          . exact And.right hpq
        . intro hq
          constructor
          . exact hp
          . exact hq


example (p q : Prop) (hp : p) : p ∨ q := by
        simp [hp]

example (p q : Prop) (hp : p) : p ∨ q := by
        . exact Or.inl hp

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
        constructor
          . exact hp
          . exact Or.inl hq

example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
        simp at *
        simp [h₁, h₂]


def mk_symm (xs : List α) := 
        xs ++ xs.reverse

theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
        simp [mk_symm]

#print reverse_mk_symm


example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
        simp [reverse_mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
        simp [reverse_mk_symm] at h
        assumption


@[simp] theorem reverse_mk_symm1 (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
        simp [mk_symm]

attribute [simp] reverse_mk_symm


example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
        simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
        simp at h
        assumption

axiom test : 1 = 2
attribute [simp] test

example (a : Nat): a + 1 = a + 2 :=
        by simp


theorem t8 : if x = 0 then y + x = y else x ≠ 0 := by
        simp (config := {contextual := true})

#print t8

theorem t9 : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
        simp_arith

#print t9