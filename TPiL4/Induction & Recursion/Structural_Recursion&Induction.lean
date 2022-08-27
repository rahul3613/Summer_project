open Nat

def add : Nat → Nat → Nat
  | m, zero => m
  | m, succ n => succ (add m n)

theorem add_zero (m : Nat) : add m zero = m := rfl
theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := rfl

theorem zero_add : ∀ n, add zero n = n
  | zero => rfl
  | succ n => congrArg succ (zero_add n)

#print zero_add

def mul : Nat → Nat → Nat
  | m, zero => zero
  | m, succ n => add m (mul m n)

#eval mul 5 3
#check mul
#print mul


theorem zero_add1 : ∀ n, add zero n = n
  | zero => by simp [add]
  | succ n => by simp [add, zero_add1]


def add1 (m : Nat) : Nat → Nat
  | zero => m
  | succ n => succ (add1 m n)


def add2 (m n : Nat) : Nat :=
  match n with
  | zero => m
  | succ n => succ (add2 m n)


def fib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => (fib (n+1)) + (fib n)

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example : fib (n+2) = fib (n+1) + fib n := rfl

example : fib 7 = 21 := rfl

#eval fib 19

def fibFast (n : Nat) : Nat :=
  (loop n).1
where
  loop : Nat → Nat × Nat
    | 0   => (1, 1)
    | n+1 => let p := loop n; (p.2, p.1+p.2)

#eval fibFast 20


def fibFast1 (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0   => (1, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).1

def loop : Nat → Nat × Nat
  | 0   => (1, 1)
  | n+1 => let p := loop n; (p.2, p.1 + p.2) 
  -- firstly obtain the value of p from loop n and then use
  -- the value of p to calculate and return (p.2, p.1+p.2)

#eval loop 5


variable (C : Nat → Type u)

#check (@Nat.below C : Nat → Type u)

#reduce @Nat.below C (3 : Nat)

#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)


#reduce fib 40
#eval fib 20

#print fib


def append : List α → List α → List α
  | [], bs => bs
  | a::as, bs => a::append as bs

#eval append [1,2] [3,4]

def lst : List Nat := 0::1::[2,3]
#print lst

example : append [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl

def listAdd [Add α]: List α → List α → List α
  | [], _ => []
  | _, [] => []
  | a::as, b::bs => (a+b)::listAdd as bs


#eval listAdd [1, 2, 3, 4] [3, 4, 5, 6, 7, 8, 9]
