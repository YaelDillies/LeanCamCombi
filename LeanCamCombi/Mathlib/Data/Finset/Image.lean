import Mathlib.Data.Finset.Image
import LeanCamCombi.Mathlib.Data.Set.Function

namespace Finset
variable {α β : Type*} [DecidableEq β] {s t : Finset α} {f : α → β}

lemma disjoint_image' (hf : Set.InjOn f (s ∪ t)) :
    Disjoint (image f s) (image f t) ↔ Disjoint s t := mod_cast Set.disjoint_image' hf

end Finset
