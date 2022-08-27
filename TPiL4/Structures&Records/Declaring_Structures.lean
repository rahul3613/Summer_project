/-
structure Point (α : Type u) where
  mk :: (x : α) (y : α)

def p := Point.mk 3 5

#reduce p
#eval Point.x p
#eval p.x
#eval Point.y p
#eval p.y


#check Point
#check @Point.rec
#check @Point.mk
#check @Point.x
#check @Point.y


structure Point1 (α : Type u) where
  x : α
  y : α

#eval Point.x (Point.mk 10 20)
#eval Point.y (Point.mk 10 20)

open Point

example (a b : α) : x (mk a b) = a := rfl

example (a b : α) : y (mk a b) = b := rfl

def p1 := Point.mk 10 20

#check p1.x
#eval p1.x
#eval p1.y
-/

structure Point (α : Type u) where
  x : α 
  y : α 
  deriving Repr

def Point.add (p q : Point Nat) := mk (p.x + q.x) (p.y + q.y)

def p := Point.mk 1 2
def q := Point.mk 3 4

#eval p.add q
#eval Point.add p q


def Point.smul (p : Point Nat) (n : Nat) :=
  Point.mk (n*p.x) (n*p.y)

#eval p.smul 4
#eval Point.smul p 4

#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x

#eval xs.map f
#eval List.map f xs