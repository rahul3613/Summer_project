namespace hidden

class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α

example (α : Type u) : (Nonempty α) ↔ (∃ x : α, True) :=
   Iff.intro
    (fun ⟨a⟩ => ⟨a, trivial⟩)
    (fun ⟨a, h⟩ => ⟨a⟩)


open Classical
namespace hidden
universe u

axiom choice {α : Sort u} : Nonempty α → α

noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop)
                                        (h : ∃ x, p x) : {x // p x} := 
                choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩

noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property

end hidden

theorem inhabited_of_nonempty : Nonempty α → Inhabited α :=
  fun h => choice (let ⟨a⟩ := h; ⟨⟨a⟩⟩)


universe u
#check (@strongIndefiniteDescription :
          {α : Sort u} → (p : α → Prop)
          → Nonempty α → {x // (∃ (y : α), p y) → p x} )


#check (@epsilon : {α : Sort u} → [Nonempty α] → (α → Prop) → α)

#check (@epsilon_spec : ∀ {α : Sort u} {p : α → Prop} (hex : ∃ (y : α), p y),
          p (@epsilon _ (nonempty_of_exists hex) p))

#check @Classical.choice