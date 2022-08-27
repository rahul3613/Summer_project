namespace hidden

structure Add (a : Type) where
   add : a → a → a

def double (s : Add a) (x : a) : a :=
  s.add x x

def Nat.add1 (x y : Nat) : Nat := Nat.add x (2*y)

#eval double {add := Nat.add} 10
#eval double {add := Nat.add1} 10
#eval double {add := Nat.mul} 10

#eval double {add := Int.add} (-10)

end hidden


namespace hidden1

class Add (a : Type) where
   add : a → a → a

instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add


#eval Add.add 4 7
#eval Add.add 4 (-7)

#check @hidden.Add.add
#check @Add.add

end hidden1



instance [Add a] : Add (Array a) where
  add x y := Array.zipWith x y (.+.)

#eval Add.add 2 3
#eval Add.add #[1, 2] #[3, 4]
#eval #[1, 2] + #[3, 4]

#check @Array.zipWith


namespace hidden

class Inhabited (a : Type) where
  default : a

instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 0
  
instance : Inhabited Int where
  default := 1

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True


#eval (Inhabited.default : Bool)
#eval (Inhabited.default : Nat)
#eval (Inhabited.default : Unit)
#eval (Inhabited.default : Int)


export Inhabited (default)

#eval (default : Nat)
#eval (default : Bool)

end hidden