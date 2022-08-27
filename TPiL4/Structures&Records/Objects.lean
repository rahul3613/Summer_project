structure Point (α : Type u) where
  x : α 
  y : α
  deriving Repr

#check {x := 10, y := 20 : Point Nat}
#check {y := 20, x := 10 : Point _}
#check ({x := 10, y := 20} : Point Nat)

example : Point Nat := {y := 20, x := 10}

structure MyStruct where
  {α : Type u}
  {β : Type v}
  a : α 
  b : β
  
#check {a := 10, b := true : MyStruct}


def p : Point Nat := {x := 1, y := 2}

#eval {p with y := 3}
#eval {p with x := 4}

def pu := {p with x := 4}

structure Point3 (α : Type u) where
  x : α 
  y : α 
  z : α 
  deriving Repr

def q : Point3 Nat := {x := 5, y := 5, z := 5}

def r : Point3 Nat := {p, q with x := 6}

#eval r

example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl