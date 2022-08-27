namespace hidden

universe u v

axiom Quot : {α : Sort u} → (α → α → Prop) → Sort u

axiom Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r

axiom Quot.ind : 
      ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
      (∀ a, β (Quot.mk r a)) → (q : Quot r) → β q

axiom Quot.lift :
      {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
      → (∀ a b, r a b → f a = f b) → Quot r → β

axiom Quot.sound : 
    ∀ {α : Type u} {r : α → α → Prop} {a b : α},
    r a b → Quot.mk r a = Quot.mk r b

end hidden


def mod7Rel (x y : Nat) : Prop := (x % 7) = (y % 7)

#check ((Quot mod7Rel) : Type)

#check (Quot.mk mod7Rel) 4

def f (x : Nat) : Bool := x % 7 = 0

theorem f_respects (a b : Nat) (h : mod7Rel a b) : f a = f b := by
  simp [mod7Rel, f] at *
  rw [h]

#check (Quot.lift f f_respects : (Quot mod7Rel) → Bool)

example (a : Nat) : Quot.lift f f_respects (Quot.mk mod7Rel a) = f a := rfl


#print f_respects

#reduce mod7Rel 3 15


namespace hidden

class Steoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r

#check Equivalence.

instance {α : Sort u} [Setoid α] : HasEquiv α := ⟨Setoid.r⟩

namespace Setoid

variable {α : Sort u} [Setoid α]

theorem refl (a : α) : a ≈ a := Setoid.iseqv.refl a

theorem symm {a b : α} (hab : a ≈ b) : b ≈ a := Setoid.iseqv.symm hab

theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c := Setoid.iseqv.trans hab hbc

end Setoid
end hidden


namespace hidden

def Quotient {α : Sort u} (s : Setoid α) := @Quot α Setoid.r

end hidden

universe u
#check (@Quotient.exact : 
          ∀ {α : Sort u} {s : Setoid α} {a b : α},
            Quotient.mk s a = Quotient.mk s b → a ≈ b)

private def eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
    ((p₁.1 = p₂.1) ∧ (p₁.2 = p₂.2)) ∨ ((p₁.1 = p₂.2) ∧ (p₁.2 = p₂.1))

infix:50 " ∼ " => eqv

private theorem eqv.refl (p : α × α) : p ∼ p := Or.inl ⟨rfl, rfl⟩ 

private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ∼ p₂ → p₂ ∼ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) => Or.inl (⟨a₁b₁.symm, a₂b₂.symm⟩)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) => Or.inr (⟨a₂b₁.symm, a₁b₂.symm⟩)

private theorem eqv.symm1 : ∀ {p₁ p₂ : α × α}, p₁ ∼ p₂ → p₂ ∼ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) => Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) => Or.inr (by simp [*] )

private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, (p₁ ∼ p₂) → (p₂ ∼ p₃) → (p₁ ∼ p₃)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), (Or.inl ⟨a₁b₁, a₂b₂⟩), (Or.inl ⟨b₁c₁, b₂c₂⟩)
      => Or.inl (⟨a₁b₁.trans b₁c₁, a₂b₂.trans b₂c₂⟩)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), (Or.inl ⟨a₁b₁, a₂b₂⟩), (Or.inr ⟨b₁c₂, b₂c₁⟩)
      => Or.inr (⟨a₁b₁.trans b₁c₂, a₂b₂.trans b₂c₁⟩)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), (Or.inr ⟨a₁b₂, a₂b₁⟩), (Or.inl ⟨b₁c₁, b₂c₂⟩)
      => Or.inr (⟨a₁b₂.trans b₂c₂, a₂b₁.trans b₁c₁⟩)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), (Or.inr ⟨a₁b₂, a₂b₁⟩), (Or.inr ⟨b₁c₂, b₂c₁⟩)
      => Or.inl (⟨a₁b₂.trans b₂c₁, a₂b₁.trans b₁c₂⟩)

private theorem eqvtrans : ∀ {p₁ p₂ p₃ : α × α}, (p₁ ∼ p₂) → (p₂ ∼ p₃) → (p₁ ∼ p₃)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), (Or.inl ⟨a₁b₁, a₂b₂⟩), (Or.inl ⟨b₁c₁, b₂c₂⟩)
      => Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), (Or.inl ⟨a₁b₁, a₂b₂⟩), (Or.inr ⟨b₁c₂, b₂c₁⟩)
      => Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), (Or.inr ⟨a₁b₂, a₂b₁⟩), (Or.inl ⟨b₁c₁, b₂c₂⟩)
      => Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), (Or.inr ⟨a₁b₂, a₂b₁⟩), (Or.inr ⟨b₁c₂, b₂c₁⟩)
      => Or.inl (by simp_all)


private theorem is_equivalence : Equivalence (@eqv α) := 
  {refl := eqv.refl, symm := eqv.symm, trans := eqv.trans}


instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

def mk {α : Type} (a₁ a₂ : α) : UProd α := 
  Quotient.mk' (a₁, a₂)

notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂

theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  Quot.sound (Or.inr ⟨rfl, rfl⟩)

private def mem_fun (a : α) : α × α → Prop
  | (a₁, a₂) => a = a₁ ∨ a = a₂

#reduce mem_fun 4 (3, 4)

private theorem mem_swap {a : α} : 
                ∀ {p : α × α}, mem_fun a p = mem_fun a (⟨p.2, p.1⟩)
  | (a₁, a₂) => by
    apply propext
    apply Iff.intro
    . intro 
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h


private theorem mem_respects
      : {p₁ p₂ : α × α} → (a : α) → p₁ ∼ p₂ → mem_fun a p₁ = mem_fun a p₂
    | (a₁, a₂), (b₁, b₂), a, (Or.inl ⟨a₁b₁, a₂b₂⟩) => by simp_all
    | (a₁, a₂), (b₁, b₂), a, (Or.inr ⟨a₁b₂, a₂b₁⟩) => by simp_all; apply mem_swap

def mem (a : α) (u : UProd α) : Prop := 
  Quot.liftOn u (fun p => mem_fun a p) (fun p₁ p₂ e => mem_respects a e)

infix:50 (priority := high) " ∈ " => mem

theorem mem_mk_left (a b : α) : a ∈ {a, b} := Or.inl rfl

theorem mem_mk_right (a b : α) : b ∈ {a, b} := Or.inr rfl

theorem mem_or_mem_of_mem_mk {a b c : α} : c ∈ {a, b} → c = a ∨ c = b :=
    fun h => h

#print mem_or_mem_of_mem_mk
end UProd

#reduce ⟨4, 5⟩ = (4, 5)
#check Quotient
