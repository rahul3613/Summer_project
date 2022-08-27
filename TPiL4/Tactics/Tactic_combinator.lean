example (p q : Prop) (hp : p) : p ∨ q := by
  apply Or.inl hp

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  exact hp
  exact hq
  
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption

example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  apply Or.inl hp

variable (p q r : Prop)
#check p ∨ (q ∨ r)

theorem t0 (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl hp | apply Or.inr | assumption)

#print t0

theorem t1 (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

#print t1

theorem t2 (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

#print t2

theorem t3 (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

#print t3

theorem t4 (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  . exact hp
  . constructor
    . exact hq
    . exact hr


example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption


example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  constructor
  . exact hp
  . constructor
    . constructor
      . constructor
        . exact hp
        . exact hq
      . exact hr
    .constructor
      . exact hq
      . constructor
        . exact hr
        . exact hp

theorem t5 (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption

#print t5

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption ))