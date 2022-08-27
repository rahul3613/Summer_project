variable (α : Sort u)
variable (r : α → α → Prop)

#check (Acc r : α → Prop)
#check (WellFounded r : Prop)

#check @Acc
#check @WellFounded


set_option codegen false

def f {α : Sort u}
      (r : α → α → Prop)
      (h : WellFounded r)
      (C : α → Sort v)
      (F : (x : α) → ((y : α) → r y x → C y) → C x)
      : (x : α) → C x := WellFounded.fix h F


open Nat

theorem div_lemma {x y : Nat} : (0 < y) ∧ (y ≤ x) → (x-y) < x :=
  fun h => sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : (0 < y) ∧ (y ≤ x) then
    f (x-y) (div_lemma h) y + 1
  else
    zero

set_option codegen false
def div := WellFounded.fix (measure id).wf div.F

#reduce div 8 2


def div1 (x y : Nat) : Nat :=
  if h : (0 < y) ∧ (y ≤ x) then
    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left
    (div1 (x - y) y) + 1
  else
    zero

#reduce div1 10 3


example (x y : Nat) : 
        div1 x y = if (0 < y) ∧ (y ≤ x) then div1 (x - y) y + 1 else 0 := by
  conv => lhs; unfold div1

example (x y : Nat) (h : 0 < y ∧ y ≤ x) : div1 x y = div1 (x-y) y + 1 := by
  conv => lhs; unfold div1
  simp [h]


set_option maxRecDepth 12345

def natToBin : Nat → List Nat
  | 0 => [0]
  | 1 => [1]
  | n =>
      have : n/2 < n := sorry
      (natToBin (n/2)) ++ [n%2]

#reduce natToBin 51


#reduce 5%3
#reduce [1,2]++[3,4,5]
#reduce 7/6


def ack : Nat → Nat → Nat
  | 0,  y => y + 1
  | x+1, 0 => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by ack x y => (x, y)

#reduce ack 0 1
#reduce ack 1 0
#reduce ack 1 1

/-
def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as.get ⟨i, h⟩
      if p a then
        go (i+1) (r.push a)
      else
        r
    else
      r
termination_by go i r => as.size - i
-/
namespace new

theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun ⟨ypos, ylex⟩ => Nat.sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos

def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    div (x - y) y + 1
  else
    0
decreasing_by apply div_lemma; assumption



def ack : Nat → Nat → Nat
  | 0,  y => y + 1
  | x+1, 0 => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by ack x y => (x, y)
decreasing_by
  simp_wf
  first | apply Prod.Lex.right; simp_arith
        | apply Prod.Lex.left; simp_arith

def natToBin : Nat → List Nat
  | 0 => [0]
  | 1 => [1]
  | n => (natToBin (n/2)) ++ [n%2]
decreasing_by sorry

end new

def unsound (x : Nat) : False :=
  unsound (x+1)
decreasing_by sorry

#check unsound 0
#print axioms unsound