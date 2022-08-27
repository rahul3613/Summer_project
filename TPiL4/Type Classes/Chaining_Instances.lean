namespace hidden

class Inhabited (a : Type u) where
 default : a

instance : Inhabited Bool where
 default := true

instance : Inhabited Nat where
 default := 0
 
export Inhabited (default)

instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

#eval (default : Nat × Bool)

end hidden

instance [Inhabited b] : Inhabited (a -> b) where
  default := fun _ => default

#check (inferInstance : Inhabited Nat)

def foo : Inhabited (Nat × Nat) :=
  inferInstance

theorem ex : foo.default = (default, default) := rfl

#print inferInstance


-- To String
#eval toString (89, "Rahul")

structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

def me : Person := {name := "Rahul", age := 22}

#eval ToString.toString me
 
#eval toString ({name := "Anurag", age := 24 : Person}, "hello")

#print ToString
#eval toString 78 ++ " rahul"