variable {p q : Prop}
theorem t1 {p q : Prop} : p → q → p := fun hp : p => fun hq : q => hp

#print t1

theorem t2 : p → q → p :=
  fun hp : p => 
  fun hq : q => 
  show p from hp

#print t2

theorem t3 (hp : p) (hq : q) : p := hp
axiom hp : p
theorem t4 : q → p := t3 hp

#check t3 hp


def func (a : Nat) (b : Nat) : Nat := a
variable (a : Nat)
def fun1 : Nat → Nat := func a

#check fun1
#check fun1 4
#check fun1 4 5

axiom unsound : False

theorem ex : 1 = 0 :=
  False.elim unsound

theorem t5 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp

theorem t6 : p → q → p :=
  fun (hp : p) (hq : q) => hp

theorem t7 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)
#check t7 p q
#check t7 r s
#check t7 (r → s) (s → r)

variable (h : r → s)
#check t7 (r → s) (s → r) h


theorem t8 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  h₁ (h₂ h₃)

variable (a b c : Prop)
#check t8 a b c

