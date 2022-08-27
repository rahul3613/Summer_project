/-
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
def do_twice (α : Type) (f : α → α) (x : α) : α := f (f x)
def do_thrice (α : Type) (f : α → α) (x : α) : α := f (f (f x))

variable (α β γ : Type)
def compose (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
def do_twice (f : α → α) (x : α) : α := f (f x)
def do_thrice (f : α → α) (x : α) : α := f (f (f x))
-/

section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x: α)

  def compose := g (f x)
  def do_twice := h (h x)
  def do_thrice := h (h (h x))
end useful


#print compose
#print do_twice
#print do_thrice

#check compose