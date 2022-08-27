def isNotZero (n : Nat) : Bool :=
  match n with
  | 0 => false
  | m+1 => true

#eval isNotZero 0
#eval isNotZero 5


def filter (p : α → Bool) : List α → List α
  | [] => []
  | a::as =>
    match p a with
    | true => a::filter p as
    | false => filter p as

#eval filter isNotZero [1,0,2,0,3]

example : filter isNotZero [1, 0, 0, 3, 0] = [1, 3] := rfl


def foo (n  :Nat) (b c : Bool) :=
  5 + match n - 5, b && c with
      | 0,   true => 0
      | m+1, true => m + 7
      | 0,   false => 5
      | m+1, false => m + 3

#eval foo 5 true true
#eval foo 6 true true
#eval foo 5 true false
#eval foo 6 true false


def bar₁ : Nat × Nat → Nat
  | (m, n) => m + n

def bar₂ (p : Nat × Nat) : Nat :=
  match p with
  | (m, n) => m + n

def bar₃ : Nat × Nat → Nat :=
  fun (m, n) => m + n

def bar₄ (p : Nat × Nat) : Nat :=
  let (m, n) := p; m + n

#eval bar₁ (3, 4)
#eval bar₂ (3, 4)
#eval bar₃ (3, 4)
#eval bar₄ (3, 4)


variable (p q : Nat → Prop)

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, ⟨px, qy⟩⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y) : ∃ x y, p x ∧ q y :=
  match h₀, h₁ with
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, ⟨px, qy⟩⟩

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
  fun ⟨x, px⟩ ⟨y, qy⟩ => ⟨x, y, ⟨px, qy⟩⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y) : ∃ x y, p x ∧ q y :=
  let ⟨x, px⟩ := h₀;
  let ⟨y, qy⟩ := h₁;
  ⟨x, y, ⟨px, qy⟩⟩
