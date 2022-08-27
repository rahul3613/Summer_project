example : ∃ x : Nat, x > 0 :=
  have h : 2 > 0 := Nat.zero_lt_succ 1
  Exists.intro 2 h

variable (h : 4 > 0)
#print Nat.zero_lt_succ

#check @Exists.intro

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) :
  ∃ w, (x < w) ∧ (w < z) :=
    Exists.intro y (And.intro hxy hyz)


example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩  

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) :
  ∃ w, (x < w) ∧ (w < z) :=
    ⟨y, And.intro hxy hyz⟩

variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0) 

#check g
#check hg


theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩ 
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩ 
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩


set_option pp.explicit true
#print gex1
#print gex2
#print gex3
#print gex4

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := 
  Exists.elim h
    (fun w =>
      fun hw : p w ∧ q w =>
      show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)


example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩ 


example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩ 


example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩


example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩


example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩


def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc
        a + b = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2) := by rw [Nat.mul_add])))


theorem even_plus_even1 (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
  Exists.intro (w1 + w2)
    (calc
      a + b = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
      _ = 2 * (w1 + w2) := by rw [Nat.mul_add])))


theorem even_plus_even2 (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩


open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)