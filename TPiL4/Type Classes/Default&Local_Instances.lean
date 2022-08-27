namespace hidden

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check_failure fun y => xs.map (fun x => hMul x y)
#check hMul (1:Int) (2:Int)

end hidden


namespace hidden1

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

@[defaultInstance]
instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check fun y => xs.map (fun x => hMul x y)
#check hMul 1 2

end hidden1


structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

@[defaultInstance 200]
instance : OfNat Rational n where
  ofNat := {num := n, den := 1, inv := by decide}

instance : ToString Rational where
  toString r:= s!"{r.num}/{r.den}"

#check 2


namespace test

class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[defaultInstance]
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class Mul (α : Type u) where
  mul : α → α → α 

@[defaultInstance 10]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

infixl:170 " * " => HMul.hMul

#check @HMul.hMul
#check @Mul.mul

end test


-- Local Instances
structure Point where
  x : Nat
  y : Nat

structure Point3 where
  x : Nat
  y : Nat
  z : Nat

section test

local instance : Add Point where
  add a b := {x := a.x + b.x, y := a.y + b.y}

def double (p : Point) := 
  Add.add p p

def pnt := {x := 4, y :=6 : Point}

#reduce double pnt

end test

def triple (p : Nat) := Add.add p + p + p

#reduce double pnt


-----
instance addPoint : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double1 (p : Point) := p + p

attribute [-instance] addPoint

def triple (p : Point) := p + p + p


-- Scoped Instance

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

instance : Add Point3 where
  add a b := { x := a.x + b.x, y := a.y + b.y, z := a.z + b.z}

def double (p : Point) :=
  Add.add p p

end Point

#check fun (p : Point) => Add.add p p 

namespace Point
#check fun (p : Point) => Add.add p p
end Point

open scoped Point
#check fun (p : Point) => Add.add p p
#check fun (p : Point3) => Add.add p p
#check fun (p : Point) => double p