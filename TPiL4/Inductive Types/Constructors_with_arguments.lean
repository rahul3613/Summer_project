namespace hidden

--inductive Prod (α : Type u) (β : Type v)
--  | mk : α → β → Prod α β

--inductive Sum (α : Type u) (β : Type v) where
--  | inl : α → Sum α β
--  | inr : β → Sum α β


def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a b => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk a b => b


def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun p => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)

def prod_example1 (p : Bool × Nat) : Nat :=
  match p with
  | (true, n) => (2 * n)
  | (false, n) => (2 * n + 1)

#eval prod_example1 (true, 3)

def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun s => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)
#eval sum_example (Sum.inr 3)

def sum_example1 (s : Sum Nat Nat) : Nat :=
  match s with
  | Sum.inl n => 2 * n
  | Sum.inr n => 2 * n + 1

#eval sum_example1 (Sum.inl 3)
#eval sum_example1 (Sum.inr 3)


inductive Prod (α : Type u) (β : Type v) where
  | mk (fst : α) (snd : β) : Prod α β

#check Prod.mk 2 4

inductive Sum (α : Type u) (β : Type v) where
  | inl (a : α) : Sum α β
  | inr (b : β) : Sum α β

end hidden

namespace hidden1

structure Prod (α : Type u) (β : Type v) where
mk :: (fst : α) (snd : β)

#check Prod Nat Nat
#check Prod.mk 3 5


structure colour where
  (red  : Nat) (green : Nat) (blue : Nat)
  deriving Repr

def yellow := colour.mk 255 255 0

#eval yellow
#print yellow

#eval colour.red yellow
#eval yellow.red


structure Colour where
  red  : Nat
  green : Nat
  blue : Nat
  deriving Repr

structure semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

def semi_a := semigroup.mk Nat
#print semi_a


inductive Sigma {α : Type u} (β : α → Type v) where
  | mk : (a : α) → β a → Sigma β


inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

#check Option

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α

#check Inhabited Nat 

end hidden1