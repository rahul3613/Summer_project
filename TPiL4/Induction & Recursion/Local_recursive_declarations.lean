def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α 
    | 0, as => as
    | n+1, as => loop n (a::as)
  loop n []

#eval replicate 5 "a"

def replicate1 (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α 
    | 0, _ => []
    | n+1, as => a::loop n as
  loop n []

#eval replicate1 5 "a"

#check @replicate1
#check @replicate1.loop

-------

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
              : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0 => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
  exact aux n []


def replicate2 (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α 
    | 0, as => as
    | n+1, as => loop n (a::as)
  

#eval replicate2 5 "a"


theorem length_replicate2 (n : Nat) (a : α) : (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α)
              : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0 => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]