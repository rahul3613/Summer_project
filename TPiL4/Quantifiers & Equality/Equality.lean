-- variable (a b c d: Type)

#check Eq
#check Eq.refl
#check Eq.symm
#check Eq.trans

universe u
#check @Eq
#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

variable (hab : a = b) (hcb : c = b) (hcd : c = d)
variable (α : Type)

example : Eq a d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

example : Eq a d :=
  (hab.trans (hcb.symm)).trans hcd


#check Eq.refl _
#check rfl
example : 2 + 3 = 5 := Eq.refl _
example (a : α) (b : α) : (a, b).1 = a := Eq.refl _
example (f : α → β) (a : α) :
  (fun x => f x) a = f a := Eq.refl _


example : 2 + 3 = 5 := rfl
example (a : α) (b : α) : (a, b).1 = a := rfl
example (f : α → β) (a : α) :
  (fun x => f x) a = f a := rfl

variable (α : Type) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a)
example : p b :=
    Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
      h1 ▸ h2

variable (α : Type) (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b) (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁


variable (a b c d : Nat)
example : a + 0 = a := Nat.add_zero _
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one _
example : 1 * a = a := Nat.one_mul _
theorem t1 : a + b = b + a := Nat.add_comm _ _
#print t1

example : (a + b) + c = a + (b + c) := Nat.add_assoc _ _ _
example : a * b = b * a := Nat.mul_comm _ _
example : (a * b) * c = a * (b * c) := Nat.mul_assoc _ _ _
example : a * (b + c) = a * b + a * c := Nat.mul_add _ _ _
example : a * (b + c) = a * b + a * c := Nat.left_distrib _ _ _
example : (a + b) * c = a * c + b * c := Nat.add_mul _ _ _ 
example : (a + b) * c = a * c + b * c := Nat.right_distrib _ _ _

example (x y z : Nat) : x * (y + z) = x * y + x * z := Nat.left_distrib _ _ _
example (x y z : Nat) : (x + y) * z = x * z + y * z := Nat.add_mul _ _ _
example (x y z : Nat) : x + y + z = x + (y + z) := Nat.add_assoc _ _ _


example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y := Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) := (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
