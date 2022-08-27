namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  namespace bar
    def ffa : Nat := f (f a)

    #check fa
    #check ffa
  end bar

  #check fa
  #check bar.ffa
end Foo

#check Foo.fa
#check Foo.bar.ffa



open Foo
#check fa
#check bar.ffa


namespace Foo
  def ffa : Nat := f (f a)
end Foo

/-
#check List.nil
#check List.cons
#check List.map

open List
#check nil
#check cons
#check map

#print List
-/