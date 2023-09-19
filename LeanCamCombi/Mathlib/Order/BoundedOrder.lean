import Mathlib.Order.BoundedOrder

section
variable {α : Type*} [PartialOrder α]

instance OrderBot.instSubsingleton : Subsingleton (OrderBot α) where
  allEq := by rintro @⟨⟨a⟩, ha⟩ @⟨⟨b⟩, hb⟩; congr; exact le_antisymm (ha _) (hb _)

instance OrderTop.instSubsingleton : Subsingleton (OrderTop α) where
  allEq := by rintro @⟨⟨a⟩, ha⟩ @⟨⟨b⟩, hb⟩; congr; exact le_antisymm (hb _) (ha _)

end
