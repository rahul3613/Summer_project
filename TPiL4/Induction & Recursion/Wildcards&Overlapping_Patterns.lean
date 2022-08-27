def foo : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2


def foo1 : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2

#eval foo1 1 1
#eval foo1 0 0
#eval foo1 0 1

#print foo1

def foo2 : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2

#eval foo2 1 1
#eval foo2 0 0
#eval foo2 0 1


def f1 : Nat → Nat → Nat
  | 0, _ => 1
  | _, 0 => 2
  | _, _ => default  -- the "incomplete case"

#eval f1 2 7
#eval f1 0 7

example : f1 0 0 = 1 := rfl
example : f1 0 (a+1) = 1 := rfl
example : f1 (a+1) 0 = 2 := rfl

example : f1 (a+1) (b+1) = 0 := rfl
example : f1 (a+1) (b+1) = default := rfl


def f2 : Nat → Nat → Option Nat
  | 0, _ => some 1
  | _, 0 => some 2
  | _, _ => none  -- the "incomplete case"

#eval f2 2 7
#eval f2 0 7

example : f2 0 0 = some 1 := rfl
example : f2 0 (a+1) = some 1 := rfl
example : f2 (a+1) 0 = some 2 := rfl

example : f2 (a+1) (b+1) = none := rfl
example : f2 (a+1) (b+1) = default := rfl


def bar : Nat → List Nat → Bool → Nat
  | 0,    _,    false => 0
  | 0,    b::_, _     => b
  | 0,    [],   true  => 7
  | a+1,  [],   false => a
  | a+1,  [],   true  => a+1
  | a+1,  b::_, _     => a+b


def foo3 : Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _   => 3


#print foo3
#print foo3.match_1