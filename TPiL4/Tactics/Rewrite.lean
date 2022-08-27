theorem t1 (f : Nat → Nat) (k : Nat)
(h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂]
  rw [h₁]

#print t1

theorem t2 (f : Nat → Nat) (k : Nat)
(h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
  calc
    f k = f 0 := by rw [h₂]
    _ = 0 := by rw [h₁]

#print t2

theorem t3 (x y : Nat) (p : Nat → Prop) (q : Prop)
(h : q → x = y) (h' : p y) (hq : q) : p x := by
  rw [h hq]; assumption


theorem t (x y : Nat) (p : Nat → Prop) (q : Prop)
(h : q → x = y) (h' : p y) (hq : q) : p x := by
  rw [(h hq).symm] at h'
  exact h'

#print t3

example (f : Nat → Nat) (k : Nat)
(h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]


example (f : Nat → Nat) (a b : Nat)
(h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]


example (a b c : Nat) : a + b + c = a + c + b :=
  calc
    a + b + c = a + (b + c) := by rw [Nat.add_assoc]
    _ = a + (c + b) := by rw [Nat.add_comm b]
    _ = a + c + b := by rw [←Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b _]

example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  calc
    f a = f (a + 0) := by rw [Nat.add_zero]
    _ = f 0 := by rw [h]

example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]


def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }


example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
    rw [h] at t
    exact t