--Namespace

namespace Foo
def bar : Nat := 1
export Nat (succ add sub)
end Foo

def Foo.bar1 : Nat := 2

open Foo
#check bar
#check Foo.bar1


def String.add (a b : String) : String := a ++ b
#eval String.add "a" "b"

def Bool.add (a b : Bool) : Bool := a != b
#eval Bool.add True True

def add (α β : Type) : Type := Sum α β

open Bool
open String
#check add
close 

#check Bool.add
#check String.add
#check _root_.add

#check add "hello" "world"
#check add true false
#check add Nat String


protected def Foo.bar2 : Nat := 2

open Foo
#check Foo.bar2
#check bar2

/-
open Nat (succ zero gcd)
#eval zero
#eval succ 1
#eval gcd 12 18


open Nat hiding succ gcd
#eval Nat.succ 0
#eval succ 0
#eval zero

open Nat renaming mul → times, add → plus
#eval plus (times 2 3) 4
-/

#eval Foo.add 5 4


--Attributes

def isPrifix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

@[simp] theorem List.isPrifix_self (as : List α) : isPrifix as as :=
  ⟨[], by simp⟩

example : isPrifix [1, 2, 3] [1, 2, 3] := by simp

attribute [simp] List.isPrifix_self


#check LE Nat