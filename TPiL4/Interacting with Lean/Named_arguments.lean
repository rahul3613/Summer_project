def sum (xs : List Int) :=
  xs.foldl (init := 0) (.+.)

#eval sum [1, 2, 3, 4]


example {a b : Nat} {p : Nat → Nat → Nat → Prop}
        (h₁ : p a b b) (h₂ : b = a) : 
        p a a b :=
    h₂ ▸ h₁

example {a b : Nat} {p : Nat → Nat → Nat → Prop}
        (h₁ : p a b b) (h₂ : b = a) : 
        p a a b :=
    Eq.subst h₂ h₁ (motive := fun x => p a x b)
 
#check @Eq.subst

def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
    x + y + w - z

example (x z : Nat) : f (z := z) x = x + 1 + 2 - z := rfl
example (x z : Nat) : f x (z := z) = x + 1 + 2 - z := rfl
example (x y : Nat) : f x y = fun z => x + y + 2 - z := rfl
example : f = fun x z => (x + 1 + 2 - z) := rfl

variable (x y z : Nat)
#check f x z

example (x : Nat) : f x = fun z => x + 1 + 2 - z := rfl
example (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z := rfl

def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none => a + c
  | some b => a + b + c

variable {α} [Add α]
--variable (c)
example : g = fun (a c : α) => a + c := rfl
example (x : α) : g (c := x) = fun (a : α) => a + x := rfl

example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl
example (x : α) : g x = fun (c : α) => x + c := rfl

example (x y : α) : g x y = fun (c : α) => x + y + c := rfl

#eval g (a := 1) (c := 3)
#eval g (a := 1) (c := 3) (b? := some 2)


inductive Term where
  | var (name : String)
  | num (val : Nat)
  | add (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)


#check Term.var

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderName1 : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none

example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc a b c)

example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc _ _ _)

example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)