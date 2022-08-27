inductive Vector (α : Type u) : Nat → Type u
  | nil : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector
def sample := cons
#eval Vector sample

namespace Vector

#check @Vector

end Vector