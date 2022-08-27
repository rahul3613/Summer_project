namespace hidden

inductive List (α : Type u) where
  | nil : List α
  | cons : α → List α → List α


namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as := by rw [append]

#print nil_append

theorem cons_append (a : α) (as bs : List α)
        : append (cons a as) bs = cons a (append as bs) :=
    by rfl


end List
end hidden

inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree


inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

namespace CBTree

def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

def toCBTree : Nat → CBTree
  | 0 => leaf
  | n + 1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree

end CBTree