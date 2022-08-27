variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem t1 : a = e :=
  calc
    a = b := h1
    b = c + 1 := h2
    c + 1 = d + 1 := congrArg Nat.succ h3
    d + 1 = 1 + d := Nat.add_comm _ _
    1 + d = e := Eq.symm h4

theorem t2 : a = e :=
  calc
    a = b := by rw [h1]
    b = c + 1 := by rw [h2]
    c + 1 = d + 1 := by rw [h3]
    d + 1 = 1 + d := by rw [Nat.add_comm _ _]
    1 + d = e := by rw [h4]


theorem t3 : a = e :=
  calc
    a = d + 1 := by rw [h1, h2, h3]
    d + 1 = 1 + d := by rw [Nat.add_comm]
    1 + d = e := by rw [h4]


theorem t4 : a = e :=
    by rw [h1, h2, h3, Nat.add_comm, h4]


theorem t5 : a = e :=
    by simp [h4, h3, h2, Nat.add_comm, h1]

example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    b < b + 1 := Nat.lt_succ_self b
    b + 1 ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y := by rw [←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]
