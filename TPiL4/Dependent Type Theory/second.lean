def twice (f : Nat -> Nat) (a : Nat) := f (f a)
-- #eval twice (fun x => x + 2) (10)

theorem twiceAdd (a : Nat) : twice (fun x => x + 2) a = a + 4 :=
rfl
--#eval twice (. + 2) 10

inductive Weekday where
| sunday    : Weekday
| monday    : Weekday
| tuesday   : Weekday
| Wednesday : Weekday
| thursday  : Weekday
| friday    : Weekday
| saturday  : Weekday

--#check Weekday.sunday

open Weekday
--#check monday
--#check tuesday

def natOfWeekday (d:Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | Wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

--#eval natOfWeekday monday

def isMonday : Weekday -> Bool :=
  fun
    | monday => true
    | _      => false

--#eval isMonday monday
--#eval isMonday tuesday

#eval toString 10
#eval toString (10, 20)