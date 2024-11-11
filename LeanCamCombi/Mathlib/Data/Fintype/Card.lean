import Mathlib.Data.Fintype.Card

instance Prop.instWellFoundedLT : WellFoundedLT Prop := Finite.to_wellFoundedLT
