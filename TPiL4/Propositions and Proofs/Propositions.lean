def Implies (p q : Prop) : Prop := p → q

variable (p q : Prop)
#check And
#eval And true false

structure Proof (p : Prop) := proof : p

#check Proof

axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))
variable (p q : Prop)
#check and_comm p q

axiom modus_pones (p q : Prop) : Proof p → Proof (Implies p q) → Proof q
#print modus_pones

axiom implies_intro (p q : Prop) : (Proof p → Proof q) → Proof (Implies p q)

#check Sort
#check Type 5
#check Sort 5 

variable (p : Prop)
variable (t1 t2 : p)
#check t1
#check t2