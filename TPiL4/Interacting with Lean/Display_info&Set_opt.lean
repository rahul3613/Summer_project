--Display 
#check Eq
#check @Eq
#check Eq.symm
#check @Eq.symm

#print Eq.symm

#check And
#check And.intro
#check @And.intro

def foo {α : Type u} (x : α) : α := x

#check foo
#check @foo
#print foo


--Setting Option
--set_option pp.explicit true
--set_option pp.universes true
--set_option pp.notation false

#check 2 + 2 = 4

#reduce (fun x => x + 2) = (fun x => x + 3)
#check (fun x => x + 1) 1
#eval (fun x => x + 1) 1