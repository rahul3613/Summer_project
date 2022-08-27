structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0


instance : OfNat Rational n where
  ofNat := {num := n, den := 1, inv := by decide}

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

def val := {num := 5, den := 1, inv := by decide : Rational}

#eval toString val

#eval (2 : Nat)
#eval (2 : Rational)
--#eval OfNat.ofNat Rational 2 (instOfNatRational 2)

#check nat_lit 2
#eval nat_lit 2

#check (2 : Rational)
#check (2 : Nat)
#check 2

#check OfNat
#check decide


class Monoid (α : Type u) where
  unit : α 
  op  : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α := 1


#print getUnit



-- Output Parameters

#check_failure (inferInstance : Inhabited (Nat × _))

namespace hidden

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Int Int Int where
  hMul := Int.mul

--instance : HMul Nat (Array Nat) (Array Nat) where
--  hMul a bs := bs.map (fun b => hMul a b)

instance [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3                    -- 12
#eval hMul (-5) (4 : Int)
#eval hMul 4 #[2, 3, 4]           -- #[8, 12, 16]

#eval hMul (-2) #[3, -1, 4]       -- #[-6, 2, -8]
#eval hMul 2 #[#[2, 3], #[0, 4]]  -- #[#[4, 6], #[0, 8]]

end hidden