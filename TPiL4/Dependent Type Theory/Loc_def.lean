#check let y := 2 + 2; y * y
#eval let y := 2 + 2; y * y

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2

#check let y := 2 + 2; let z := y + y; z * z
#eval let y := 2 + 2; let z := y + y; z * z

def t (x : Nat) : Nat :=
  let y := x + x
  y * y