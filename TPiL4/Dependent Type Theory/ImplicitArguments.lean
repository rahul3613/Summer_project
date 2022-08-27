/-universe u
def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst
#check Lst.cons
#check Lst.nil
#check Lst.append


#check Lst.cons 0 (Lst.nil)
def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 (Lst.nil)

#check Lst.append as bs

universe v
def ident {α : Type u} (x : α) := x
#check ident
#check ident 1
#check ident "Hello"
#check @ident
-/

universe w
section
  variable {α : Type w}
  def ident (x : α) := x
end

#check ident
#check ident 4
#check ident "hello"

#check 2
#check (2 : Nat)
#check (2 : Int)

#check List.nil
#check id


#check @id
#check @id Nat
#check @id Bool

#check @id Nat 1
#check id 1
