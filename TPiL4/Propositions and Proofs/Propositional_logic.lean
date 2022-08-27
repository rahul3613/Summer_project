-- Conjuction 

variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
#check fun (hp : p) (hq : q) => And.intro hp hq

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

#check Prop

variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)
#check And.intro hp hq

variable (xs : List Nat)
#check List.length xs
#check xs.length

example (h : p ∧ q) : q ∧ p :=
  ⟨(h.right), (h.left)⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩
example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩


--Disjunction
variable (p q r : Prop)
theorem t9 (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

#check t9
#check Or.elim

theorem t10 (h : p ∨ q) : (q ∨ p) := 
  Or.elim h 
    (fun hp : p =>
      show q ∨ p from Or.intro_right _ hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left _ hq)

#print t10

example (h : p ∨ q) : q ∨ p := 
  Or.elim h (fun hp : p => Or.inr hp) (fun hq : q => Or.inl hq)

example (h : p ∨ q) : q ∨ p := 
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)



#check Or.elim
#check fun hp =>
      Or.inr hp


-- Nagation and Falsity
variable (p q : Prop)

theorem t11 (hpq : p → q) (hnq : ¬q) : ¬p := 
  fun hp : p => 
    show False from hnq (hpq hp)

#print t11

variable (p1 : p)
variable (p2 : ¬p)

#check False.elim

variable (tq q : Prop)
theorem t12 (hp : p) (hnp : ¬p) : q :=
  False.elim (hnp hp)

#print t12

example (hp : p) (hnp : ¬p) : q :=
  absurd hp hnp

theorem t13 (hnp : ¬p) ( hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp


-- Logical Equivalence
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro 
  (fun h : p ∧ q =>
  show q ∧ p from And.intro h.right h.left) 
  (fun h : q ∧ p =>
  show p ∧ q from And.intro h.right h.left)

#check and_swap p q
variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h

#check and_swap p q

theorem and_swap1 : p ∧ q ↔ q ∧ p :=
  ⟨fun h => ⟨ h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example : q ∧ p := (and_swap1 p q).mp h