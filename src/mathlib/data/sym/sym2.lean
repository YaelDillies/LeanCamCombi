import data.sym.sym2

open function

variables {α β : Type*} {e : sym2 α} {f : α → β}

namespace sym2

protected lemma is_diag.map : e.is_diag → (e.map f).is_diag := sym2.ind (λ x y, congr_arg f) e

lemma is_diag_map (hf : injective f) : (e.map f).is_diag ↔ e.is_diag :=
sym2.ind (λ x y, hf.eq_iff) e

end sym2
