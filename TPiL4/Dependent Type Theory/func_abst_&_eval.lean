def F (x : Nat) := x + 5
#eval F 4

#check fun (x : Nat) => x + 5
#check λ (x : Nat) => x + 5

#check fun x : Nat => x + 5
#check λ x : Nat => x + 5

#eval (λ x : Nat => x + 5) 10

#check fun x : Nat => fun y : Bool => if not y then x+1 else x+2
#check fun (x : Nat) (y : Bool) => if not y then x+1 else x+2
#check fun x y => if not y then x+1 else x+2

def f (n : Nat) : String := toString n
#eval f 6

def g (s : String) : Bool := s.length > 0
#eval g "cjx"

#check fun x : Nat => x
#check fun x : Nat => true
#check fun x : Nat => g (f x)
#check fun x => g (f x)

#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)

#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)

#check (fun x : Nat => x) 1
#check (fun x : Nat => true) 1

#eval (fun x : Nat => x) 1
#eval (fun x : Nat => true) 1

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0