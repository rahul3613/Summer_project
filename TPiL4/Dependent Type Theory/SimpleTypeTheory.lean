/- Simple Type Theory -/

def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

#check m
#check n

#check n+0
#check m*(n+0)

#check b1
#check b1 && b2
#check b1 || b2
#check true

#eval 5*4
#eval m+2
#eval b1 && b2


/- New Types out of Others -/

#check Nat → Nat
#check Nat -> Nat

#check Nat × Nat
#check Prod Nat Nat

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat

#check Nat.succ
#check (0, 1)
#check Nat.add

#eval m.add 5

#eval Nat.succ 2
#eval m.succ

#check Nat.add 3
#eval m.add (3)

#check Nat.add 3 5
#eval Nat.add 3 5

#check (5, 9).1
#eval  (5, 9).1

#check (5, 9).2
#eval  (5, 9).2