open Classical

variable (p q : Prop) (h : ¬¬p)
#check em p

theorem dne (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

-- False.elim (hnp p) = absurd hnp h

#check Or.elim
#check fun hp : p => hp
#check fun hnp : ¬p => absurd hnp h

theorem dne1 (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)

#print dne
#print dne1

theorem dne2 (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
      show False from h h1)

#print dne2

theorem t1 (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr 
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)

#print t1