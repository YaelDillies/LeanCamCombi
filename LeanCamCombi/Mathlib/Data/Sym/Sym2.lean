import Mathbin.Data.Sym.Sym2

#align_import mathlib.data.sym.sym2

open Function

variable {α β : Type _} {e : Sym2 α} {f : α → β}

namespace Sym2

protected theorem IsDiag.map : e.IsDiag → (e.map f).IsDiag :=
  Sym2.ind (fun x y => congr_arg f) e

theorem isDiag_map (hf : Injective f) : (e.map f).IsDiag ↔ e.IsDiag :=
  Sym2.ind (fun x y => hf.eq_iff) e

end Sym2

