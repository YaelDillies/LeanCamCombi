import Mathlib.Data.Sym.Sym2

open Function

variable {α β : Type*} {e : Sym2 α} {f : α → β}

namespace Sym2

protected lemma IsDiag.map : e.IsDiag → (e.map f).IsDiag := Sym2.ind (fun _ _ ↦ congr_arg f) e

lemma isDiag_map (hf : Injective f) : (e.map f).IsDiag ↔ e.IsDiag :=
  Sym2.ind (fun _ _ ↦ hf.eq_iff) e

end Sym2
