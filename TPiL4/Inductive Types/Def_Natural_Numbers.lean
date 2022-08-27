/-namespace hidden

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | hidden.Nat.zero => m
  | hidden.Nat.succ n => hidden.Nat.succ (add m n)

open Nat
#eval add (succ (succ zero)) (succ zero)

end hidden

#print hidden.Nat 

def zero := hidden.Nat.zero
#print zero

#check @Nat.rec


namespace hidden
namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | zero => m
  | succ n => succ (add m n)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
#print add_zero

theorem add_succ (m : Nat) : m + succ n = succ (m + n) := rfl
#print add_succ


end Nat
end hidden
-/

namespace hidden
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
   n
   (show 0 + 0 = 0 from rfl)
   (fun (n : Nat) (ih : 0 + n = n) =>
    show 0 + succ n = succ n from
    calc
       0 + succ n = succ (0 + n) := rfl
                _ = succ n       := by rw [ih])


theorem zero_add1 (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
   n
   rfl
   (fun n ih => by simp [add_succ, ih])

#print zero_add1


theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k))
    k
    (show m + n + 0 = m + (n + 0) from rfl)
    (fun (k : Nat) (ih : m + n + k = m + (n + k)) =>
      show m + n + succ k = m + (n + succ k) from
      calc
        (m + n) + succ k = succ ((m + n) + k) := by rfl
        _ = succ (m +(n + k)) := by rw [ih]
        _ = m + succ (n + k) := by rfl
        _ = m + (n + succ k) := rfl)


theorem add_assoc1 (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k))
    k
    rfl
    (fun k ih => by simp [add_succ, ih])


theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun n => m + n = n + m)
    n
    (show m + 0 = 0 + m from
      calc
        m + 0 = m := by rw [Nat.add_zero]
            _ = 0 + m := by rw [Nat.zero_add])
    (fun (n : Nat) (ih : m + n = n + m) =>
      show m + succ n = succ n + m from
      calc
        m + succ n = succ (m + n) := by rfl
        _ = succ (n + m) := by rw [ih]
        _ = succ n + m := by rw [succ_add])


theorem succ_add (n m : Nat) : (succ n) + m = succ (n + m) :=
  Nat.recOn (motive := fun m => (succ n) + m = succ (n + m))
  m
  (show (succ n) + 0 = succ (n + 0) from
    calc
      (succ n) + 0 = succ n := by rw [Nat.add_zero]
      _ = succ (n + 0) := by rw [Nat.add_zero]
      )
  (fun (m : Nat) (ih : (succ n) + m = succ (n + m)) =>
    show succ n + succ m = succ (n + succ m) from
    calc
      succ n + succ m = succ (succ n + m) := by rfl
      _ = succ (succ (n + m)) := by rw [ih]
      _ = succ (n + succ m) := by rfl
      )

theorem succ_add1 (n m : Nat) : (succ n) + m = succ (n + m) :=
  Nat.recOn (motive := fun m => (succ n) + m = succ (n + m))
  m
  (show (succ n) + 0 = succ (n + 0) from
    calc
      (succ n) + 0 = succ n := by rw [Nat.add_zero]
      _ = succ (n + 0) := by rw [Nat.add_zero]
      )
  (fun (m : Nat) (ih : (succ n) + m = succ (n + m)) =>
    show succ n + succ m = succ (n + succ m) from
    calc
      succ n + succ m = succ (succ n + m) := by rfl
      _ = succ (succ (n + m)) := by rw [ih]
      _ = succ (n + succ m) := by rfl
      )

end hidden