/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

/-!
# Utilities for course statements

Sometimes a course states a result much earlier than it proves it, or states a theorem that won't be
proved in the course.
-/

/-- This theorem is proved later in this course. -/
axiom proved_later {P : Prop} : P

/-- This theorem is not proved in this course but will be used. -/
axiom blackboxed {P : Prop} : P

/-- This theorem is not proved in this course and won't be used. -/
axiom showcased {P : Prop} : P
