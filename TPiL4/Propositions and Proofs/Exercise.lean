variable (p q r : Prop)
open Classical

--1--
example : p ∧ q ↔ q ∧ p := 
  Iff.intro 
    (fun h : p ∧ q => And.intro h.right h.left)
    (fun g : q ∧ p => And.intro g.right g.left)


--2--
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q => 
      h.elim 
        (fun hp => Or.inr hp)
        (fun hq => Or.inl hq))
    (fun h : q ∨ p =>
      h.elim 
        (fun hp => Or.inr hp)
        (fun hq => Or.inl hq))


--3--
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
      And.intro h.left.left (And.intro h.left.right h.right))
    (fun g : p ∧ (q ∧ r) =>
      And.intro (And.intro g.left g.right.left) g.right.right)


--4--
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      h.elim
        (fun hpq : p ∨ q =>
          hpq.elim
            (fun hp : p =>
              show p ∨ (q ∨ r) from Or.inl hp)
            (fun hq : q =>
              show p ∨ (q ∨ r) from (Or.inr (Or.inl hq)))
        )
        (fun hr : r =>
          show p ∨ (q ∨ r) from Or.inr (Or.inr hr))
        )
    
    (fun g : p ∨ (q ∨ r) =>
      g.elim
        (fun hp : p =>
          show (p ∨ q) ∨ r from Or.inl (Or.inl hp))
        (fun hqr : q ∨ r =>
          hqr.elim
            (fun hq : q =>
              show (p ∨ q) ∨ r from Or.inl (Or.inr hq))
            (fun hr : r =>
              show (p ∨ q) ∨ r from Or.inr hr)
        )
      )
        

--5--
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl (And.intro hp hq))
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr (And.intro hp hr))
    )

    (fun g : (p ∧ q) ∨ (p ∧ r) =>
      g.elim
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from And.intro hp (Or.inl hq)
        )
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from And.intro hp (Or.inr hr))
    )


--6--
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun g : p ∨ (q ∧ r) =>
      g.elim
        (fun hp : p =>
          show (p ∨ q) ∧ (p ∨ r) from And.intro (Or.inl hp) (Or.inl hp))
        (fun hqr : q ∧ r =>
          have hq : q := hqr.left
          have hr : r := hqr.right
          show (p ∨ q) ∧ (p ∨ r) from And.intro (Or.inr hq) (Or.inr hr))
    )

    (fun h : (p ∨ q) ∧ (p ∨ r) =>
      have hpq : p ∨ q := h.left
      have hpr : p ∨ r := h.right

      Or.elim hpq
        (fun hp : p =>
          show p ∨ (q ∧ r) from Or.inl hp)
        (fun hq : q => 
          Or.elim hpr
            (fun hp : p =>
              show p ∨ (q ∧ r) from Or.inl hp)
            (fun hr : r =>
              show p ∨ (q ∧ r) from Or.inr ⟨hq, hr⟩))
    )


--7. Retry
theorem t1 : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun (hp : p)  =>
      fun hqr : q → r =>
      show (p ∧ q → r) from
      (And.intro hp (fun hq : q => hqr (Or.inl hp))))
    
    (fun h : p ∧ q → r =>
      show p → (q → r) from
      (fun hqr : q → r =>
       fun hq : q => hqr (Or.inl hq)
      )
      )



--8--
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h : (p ∨ q) → r =>
      show (p → r) ∧ (q → r) from
        (And.intro
          (fun hp : p => h (Or.inl hp))
          (fun hq : q => h (Or.inr hq)))
    )

    (fun h : (p → r) ∧ (q → r) =>
      show (p ∨ q) → r from
        (fun hpq : p ∨ q => 
          hpq.elim
            (fun hp : p => h.left hp)
            (fun hq : q => h.right hq)
        )
    )


--9--
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h : ¬(p ∨ q) => 
      And.intro
        (fun hp : p => h (Or.inl hp))
        (fun hq : q => h (Or.inr hq))
    )
    (fun h : ¬p ∧ ¬q =>
      have hnp : ¬p := h.left
      have hnq : ¬q := h.right
      Or.elim (em p)
        (fun hp : p => Or.inl hnp)
        (fun hq : q => Or.inl hnq)
      )


--10--
example : ¬(p ∧ q) → (¬p ∨ ¬q) :=
  (fun h : ¬(p ∧ q) =>
    Or.elim (em p)
      (fun hp : p =>
        Or.inr 
          (fun hq : q => h (And.intro hp hq))
      )
      (fun hnp : ¬p =>
        Or.inl hnp)
  )


example : p ∨ False ↔ p :=
  Iff.intro
  (fun h : p ∨ False =>
    fun hp : p =>
    show p from hp)
  (fun h : p =>
    Or.elim (em False)
      (Or.inl (False h)
      (Or.inr (fun hnq : ¬q => absurd (And.intro h hnq)))))