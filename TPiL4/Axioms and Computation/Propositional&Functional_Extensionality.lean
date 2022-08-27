-- Propositional Extensionality

namespace ex

axiom propext {a b : Prop} : (a ↔ b) → a = b

end ex

theorem thm₁ (a b c d e : Prop) (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl (c ∧ a ∧ d → e)

theorem thm₂ (a b : Prop) (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b :=
  propext h ▸ h₁

#check @propext

-- Function Extensionality
universe u v
#check (@funext :
            {α : Type u}
          → {β : α → Type u}
          → {f g : (x : α) → β x}
          → (∀ (x : α), f x = g x)
          → f = g)

#print funext


def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (a : Set α) := a x
infix:50 (priority := high) " ∈ " => mem

theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))

def num5 : Set Nat := fun x => x < 5

#reduce num5.mem 3
#check (3 ∈ num5)
#eval (fun x => x < 5) 3


def empty : Set α := fun x => False
#check empty.mem

notation (priority := high) "φ" => empty
#reduce φ

def inter (a b : Set α) : Set α := fun x => (x ∈ a) ∧ (x ∈ b)
infix:70 " ∩ " => inter

theorem inter_self (a : Set α) : a ∩ a = a :=
  setext fun x => Iff.intro
      (fun ⟨h, _⟩ => h)
      (fun h => ⟨h, h⟩)

theorem inter_empty (a : Set α) : a ∩ φ = φ :=
  setext fun x => Iff.intro
      (fun ⟨ha, h⟩ => h)
      (fun h => False.elim h)

theorem empty_inter (a : Set α) : φ ∩ a = φ :=
  setext fun x => Iff.intro
      (fun ⟨h, ha⟩ => h)
      (fun h => False.elim h)

theorem inter.comm (a b: Set α) : a ∩ b = b ∩ a :=
  setext fun x => Iff.intro
      (fun ⟨ha, hb⟩ => ⟨hb, ha⟩)
      (fun ⟨hb, ha⟩ => ⟨ha, hb⟩)

end Set


def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val : Nat := Eq.recOn (motive := fun f g => Nat) f_eq_g 0

#reduce val
#eval val


theorem tteq : (True ∧ True) = True := 
  propext (Iff.intro (fun ⟨h, _⟩ => h) (fun h => ⟨h, h⟩))

def val1 : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) tteq 0

#reduce val
#eval val
