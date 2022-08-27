import Init


section one
variable (x y : Nat)

def double := x + x

#check double y
#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y :=
  by simp [double]

example : double (x + y) = double x + double y :=
  calc
    double (x + y) = (x + y) + (x + y) := by rw [double]
    _ = (x + x) + (y + y) := by simp
    _ = double x + (y + y) := by rw [←double]
    _ = double x + double y := by rw [←double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]

example : double (x * y) = (double x) * y :=
  calc
    double (x * y) = (x * y) + (x * y) := by rw [double]
    _ = (x + x) * y := by rw [Nat.add_mul]
    _ = (double x) * y := by rw [←double]

#print t2


#check Nat.add_mul x x y

end one