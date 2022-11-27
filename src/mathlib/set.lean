import data.set.basic

variables {α : Type*}

namespace set

@[simp] lemma preimage_mem_singleton_true (s : set α) : (∈ s) ⁻¹' {true} = s := by { ext, simp }
@[simp] lemma preimage_mem_singleton_false (s : set α) : (∈ s) ⁻¹' {false} = sᶜ := by { ext, simp }

end set
