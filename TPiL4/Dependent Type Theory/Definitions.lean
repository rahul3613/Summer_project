/-
def double (x : Nat) : Nat := x + x
#eval double 3

def double : Nat → Nat :=
  fun x => x + x

#eval double 4
-/

def double :=
  fun x : Nat => x + x

#eval double 3

def pi := 3.14159
#eval pi

def add (x y : Nat) := x + y
#eval add 3 4
#eval add (double 3) 4

def add1 (x : Nat) (y : Nat) := x + y
#eval add1 (double 3) (5 + 7)

def greter (x y : Nat) := 
  if x > y then x
  else y

#eval greter 3 4

def doTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
#eval doTwice double 2

def compose (a b c : Type) (g : b → c) (f : a → b) (x : a) : c := g (f x)
#eval compose Nat Nat Nat double double 4