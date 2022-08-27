open Nat

def sub1 : Nat → Nat
  | zero => zero
  | succ x => x

#eval sub1 (succ (succ zero))
#eval sub1 3
#eval sub1 zero


def isZero : Nat → Bool
  | zero => True
  | succ x => False

#eval isZero 5
#eval isZero 0


example : sub1 0 = 0 := by rfl
example (x : Nat) : sub1 (succ x) = x := by rfl

example : isZero 0 = true := rfl
example (x : Nat) : isZero (succ x) = false := by rfl

example : sub1 7 = 6 := by rfl
example (x : Nat) : isZero (x + 3) = false := rfl


def Sub1 : Nat → Nat
  | 0 => 0
  | x + 1 => x

def IsZero : Nat → Bool
  | 0 => True
  | x + 1 => False


def swap : α × β → β × α
  | (a, b) => (b, a)

#eval swap (3, 4)
#eval swap (3, 4, 7)

/-
def foo : Nat × Nat → Nat
  | (a, b) => a + b

#eval foo (2, 3)
-/

def bar : Option Nat → Nat
  | some n => n + 1
  | none => 0

#eval bar (some 4)
#eval bar none


namespace hidden

def not : Bool → Bool
  | true => false
  | false => true

theorem not_not : ∀ (b : Bool), not (not b) = b
  | true => rfl
  | false => rfl

end hidden


example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h₁ h₂ => And.intro h₂ h₁

example (p q : Prop) : p ∨ q → q ∨ p
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq


def sub2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | x + 2 => x

example : sub2 0 = 0 := rfl
example : sub2 1 = 0 := rfl
example : sub2 (x + 2) = x := rfl

example : sub2 5 = 3 := rfl

#print sub2


def foo : Nat × Nat → Nat
  | (0, n)    => 0
  | (m + 1, 0) => 1
  | (m + 1, n + 1) => 2

#eval foo (0, 0)
#eval foo (0, 5)
#eval foo (2, 0)
#eval foo (2, 3)


def foo1 : Nat → Nat → Nat
  | 0,     n     => 0
  | m + 1, 0     => 1
  | m + 1, n + 1 => 2

#eval foo1 0 0
#eval foo1 0 5
#eval foo1 2 0
#eval foo1 2 3


example (p q : α → Prop)
        : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
    | Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
    | Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)


def bar1 : List Nat → List Nat → Nat
  | [],      []     => 0
  | a :: as, []     => a
  | [],      b::bs   => b
  | a :: as, b :: bs => a + b

#eval bar1 []  []
#eval bar1 [2, 1]  []
#eval bar1 []  [3,4]
#eval bar1 [2, 1]  [3, 4]

namespace hidden

def and : Bool → Bool → Bool
  | true, a => a
  | false, _ => false

#print and
#eval and true false


def or : Bool → Bool → Bool
  | true, _ => true
  | false, a => a

#eval Or true false


def cond : Bool → α → α → α 
  | true, a, b => a
  | false, a, b => b

#eval cond true 1 0
#eval cond false 1 0

end hidden


def tail1 {α : Type u} : List α → List α 
  | []      => []
  | a :: as => as

#eval tail1 [1, 2, 3]
variable (α : Type u) (lst1 : List Nat := [])
#eval tail1 [1].tail!
#eval tail1 [1].tail!


def tail2 : {α : Type u} → List α → List α 
  | _, []      => []
  | α, a :: as => as

#eval tail2 [1, 2, 3]
#eval tail2 [1].tail!


#check tail1 [1].tail!
#check []
#check lst1