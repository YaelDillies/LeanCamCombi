import Mathlib.Algebra.Order.SMul

section
variable {α β : Type*} [OrderedRing α] [OrderedAddCommGroup β] [Module α β] [OrderedSMul α β]
  {a a₁ a₂ : α} {b b₁ b₂ : β}
-- TODO: Replace `smul_le_smul_of_nonneg`
lemma smul_le_smul_of_nonneg_left (h : b₁ ≤ b₂) (ha : 0 ≤ a) : a • b₁ ≤ a • b₂ :=
smul_le_smul_of_nonneg h ha

lemma smul_le_smul_of_nonneg_right (h : a₁ ≤ a₂) (hb : 0 ≤ b) : a₁ • b ≤ a₂ • b := by
  rw [←sub_nonneg, ←sub_smul]; exact smul_nonneg (sub_nonneg.2 h) hb

lemma smul_le_smul (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (h₁ : 0 ≤ b₁) (h₂ : 0 ≤ a₂) : a₁ • b₁ ≤ a₂ • b₂ :=
  (smul_le_smul_of_nonneg_right ha h₁).trans $ smul_le_smul_of_nonneg_left hb h₂

end

section
variable {α β γ : Type*}

@[to_additive]
instance OrderDual.instSMulCommClass [SMul β γ] [SMul α γ] [SMulCommClass α β γ] :
    SMulCommClass αᵒᵈ β γ := ‹SMulCommClass α β γ›

@[to_additive]
instance OrderDual.instSMulCommClass' [SMul β γ] [SMul α γ] [SMulCommClass α β γ] :
    SMulCommClass α βᵒᵈ γ := ‹SMulCommClass α β γ›

@[to_additive]
instance OrderDual.instSMulCommClass'' [SMul β γ] [SMul α γ] [SMulCommClass α β γ] :
    SMulCommClass α β γᵒᵈ := ‹SMulCommClass α β γ›

@[to_additive OrderDual.instVAddAssocClass]
instance OrderDual.instIsScalarTower [SMul α β] [SMul β γ] [SMul α γ] [IsScalarTower α β γ] :
   IsScalarTower αᵒᵈ β γ := ‹IsScalarTower α β γ›

@[to_additive OrderDual.instVAddAssocClass']
instance OrderDual.instIsScalarTower' [SMul α β] [SMul β γ] [SMul α γ] [IsScalarTower α β γ] :
    IsScalarTower α βᵒᵈ γ := ‹IsScalarTower α β γ›

@[to_additive OrderDual.instVAddAssocClass'']
instance OrderDual.IsScalarTower'' [SMul α β] [SMul β γ] [SMul α γ] [IsScalarTower α β γ] :
    IsScalarTower α β γᵒᵈ := ‹IsScalarTower α β γ›

end
