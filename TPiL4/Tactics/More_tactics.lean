example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq


example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp


example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption


example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  assumption
  assumption


example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption


example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption


example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inl h =>
    apply Or.inr
    assumption
  case inr h =>
    apply Or.inl
    assumption


example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inl h =>
    apply Or.inr
    assumption
  . apply Or.inl
    assumption


example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq =>
    constructor
    exact hq
    exact hp


example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq => constructor; exact hp; apply Or.inl hq;
    | inr hpr =>
      cases hpr with
      | intro hp hr => constructor; exact hp; apply Or.inr hr;


example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px


example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px


example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x


def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption


def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr
    assumption
  . apply Sum.inl
    assumption


open Nat
example (P : Nat → Prop) (h₀ : P 0)
  (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by
  cases m with
  | zero => exact h₀
  | succ m' => exact h₁ m'


example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction


example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨hp, Or.inl hq⟩ => apply Or.inl; constructor; exact hp; exact hq
    | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor; exact hp; exact hr
  .intro h
    match h with
    | Or.inl ⟨hp, hq⟩ => constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ => constructor; exact hp; apply Or.inr; exact hr


example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ => apply Or.inl; constructor; exact hp; exact hq
    | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor; exact hp; exact hr
  .intro
    | Or.inl ⟨hp, hq⟩ => constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ => constructor; exact hp; apply Or.inr; exact hr