import MeasureTheory.Measure.MeasureSpace

open MeasureTheory

variable {Ω : Type _} [MeasurableSpace Ω] {μ : Measure Ω}

instance AeNeBot.to_neZero [μ.ae.ne_bot] : NeZero μ :=
  ⟨ae_neBot.1 ‹_›⟩
