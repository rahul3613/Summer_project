def f (x : Nat) {y : Nat} (z : Nat) : Nat := x + y + z
#check @f 7 8 9

/-
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c: α}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c: α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
  (reflr : reflexive r) (euclr : euclidean r)
  : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr a)


theorem th2 {α : Type u} {r : α → α → Prop}
          (symmr : symmetric r) (euclr : euclidean r)
          : transitive r :=
  fun {a b c : α} =>
  fun (h : r a b) (g : r b c) =>
  show r a c from euclr (symmr h) g

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
 @th2 _ _ (@th1 _ _ reflr @euclr) @euclr

 variable (r : α → α → Prop)
 variable (euclr : euclidean r)

 #check euclr
 #check euclidean

 -/


 def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b : α}}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
  th2 (th1 reflr euclr) euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check euclr  -- euclidean r


-- Notation
-- Notations and Precedence

/-
infixl:60 "plus" => HAdd.hAdd
#eval 4 plus 7
#eval HAdd.hAdd 4 7

notation a b " add " => HAdd.hAdd a b
#eval 4 5 add

infix:50 "equal" => Eq
#eval 5 equal 4
#eval Eq 5 4

infix:0 "∨" => HPow.hPow
#eval 5 ∨ 2
#eval HPow.hPow 5 2

prefix:0 "∧" => HPow.hPow 2
#eval ∧ 5

postfix:0 "∧" => HPow.hPow 2
#eval 5 ∧

prefix:80 "neg" => Neg.neg
#eval neg 5

postfix:max "++"  => Nat.succ
#eval 5 ++

notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs

notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg

notation:max "(" e ".)" => 2 * e
#eval ( 5 .)
-/

-- Coercions
variable (m n : Nat)
variable (i j : Int)

#check i + m
#check i + m + j
#check i + m + n
#check m + n
#check i + j