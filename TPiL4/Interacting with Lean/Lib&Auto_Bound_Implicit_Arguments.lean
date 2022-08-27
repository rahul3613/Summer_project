
example : ∀ {n m : Nat}, Nat.succ n ≤ Nat.succ m → n ≤ m :=
fun {n m} => Nat.pred_le_pred

#print Nat.succ_ne_zero
--#print Nat.noConfusion
#check Nat.zero_add
#check Nat.mul_one
#check @Nat.le_of_succ_le_succ

#print Nat.le_of_succ_le_succ

/-
@Prod.mk : {α : Type u_1} → {β : Type u_2} → α → β → α × β
-/
#check @Prod.mk
#check @Prod.fst
#check @Prod.snd
#check @Prod.rec

#check @And.intro
#check @And.casesOn
#check @And.left
#check @And.right

#check @Or.inl
#check @Or.inr

#check @Exists.intro
#check @Exists.elim

#check @Eq.refl
#check @Eq.subst


--Auto Bound Implicit Arguments
--universe u v w

--set_option autoImplicit false

def compose {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
            g (f x)


def compose1.{u, v, w}
            {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
            g (f x)


def compose2 (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check @compose2
#print compose2