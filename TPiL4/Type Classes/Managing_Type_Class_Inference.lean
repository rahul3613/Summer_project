def foo : Add Nat := inferInstance
def bar : Inhabited (Nat → Nat) := inferInstance

#check @inferInstance

#check (inferInstance : Add Nat)

#check inferInstanceAs (Add Nat)

#check @inferInstanceAs

def Set (α : Type u) := α → Prop

example : Inhabited (Set α) := inferInstance

instance : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))

/-
set_option trace.Meta.synthInstance true

set_option synthInstance.maxHeartbeats 10000
set_option synthInstance.maxSize 400
-/

class Foo where
  a : Nat
  b : Nat

instance (priority := default+1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

#eval Foo.a

instance (priority := default+2) i3 : Foo where
  a := 3
  b := 3

#eval Foo.a