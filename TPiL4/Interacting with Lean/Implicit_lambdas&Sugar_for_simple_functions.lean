#check @ReaderT
#check @ReaderT Nat
#check Monad

variable (ρ : Type) (m : Type → Type) [Monad m]
instance : Monad (ReaderT a m) where
  pure := ReaderT.pure
  bind := ReaderT.bind

def id1 : {α : Prop} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []


--Sugar For Simple Functions

#check (. + 1)
#eval (. + 1) 2
/-
fun a => a + 1 : Nat → Nat
-/
#check (2 - .) 5
#eval (2 - .) 1

def f (x y z : Nat) := x + y + z
#check (f . 1 .)
#eval (f . 1 .) 1 2
#eval (. + 1 + .) 1 2

#check (2 * .)

#eval (String.append "ab" .) "c"

#eval [1, 2, 3, 4, 5].foldl (. * .) 1
#check [1, 2, 3, 4, 5].foldl 

#check (Prod.mk · (· + 1))

#eval (Prod.mk . .) 3 4
#eval (Prod.mk  . ((· + 1) 3)) 4

#check @List.foldl
#eval [1, 2, 3, 4].foldl (. * .) 1

#eval [(1, 2), (3, 4), (5, 6)].map (·.1)
#eval [(1, 2), (3, 4), (5, 6)].map fun x => x.1