/-
inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday


#check Weekday.sunday
#check Weekday.monday

--open Weekday
#check sunday
#check monday
-/


inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  deriving Repr

#check Weekday.sunday
#check Weekday.monday

open Weekday
#check sunday
#check monday

#check Weekday.rec

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay sunday
#eval numberOfDay Weekday.monday
#eval numberOfDay Weekday.tuesday

#print numberOfDay
--#print numberOfDay.match_1
#print Weekday.casesOn
#check @Weekday.rec

#eval tuesday


namespace Weekday

def next (d : Weekday) : Weekday :=
  match d with
  | sunday => monday
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | monday => sunday
  | tuesday => monday
  | wednesday => tuesday
  | thursday => wednesday
  | friday => thursday
  | saturday => friday
  | sunday => saturday

#eval next (next tuesday)
#eval next (previous wednesday)

example : next (previous tuesday) = tuesday :=
  rfl

def next_previous (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday => rfl
  | monday => rfl
  | tuesday => rfl
  | wednesday => rfl
  | thursday => rfl
  | friday => rfl
  | saturday => rfl

def next_previous1 (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl

end Weekday


namespace Hidden

def and (a b : Bool) : Bool :=
  match b with
  | true  => a
  | false => false

def or (a b : Bool) : Bool :=
  match b with
  | true  => true
  | false => b

end Hidden