import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

/-- A probability distribution on nonnegative real types with a continuous CDF
and a nonnegative Lebesgue density, positive wherever the CDF lies strictly
between zero and one. -/
structure TypeDist where
  mu : Measure Real
  F : Real → Real
  f : Real → Real
  isProb : IsProbabilityMeasure mu
  F_continuous : Continuous F
  F_monotone : Monotone F
  f_measurable : Measurable f
  f_nonneg : ∀ t, 0 ≤ f t
  F_eq : ∀ t, F t = (mu (Set.Iic t)).toReal
  hasDensity : ∀ {s}, MeasurableSet s →
    mu s = ENNReal.ofReal (∫ t in s, f t ∂volume)
  f_eq_zero_of_neg : ∀ t, t < 0 → f t = 0
  pos_of_interior : ∀ t, 0 < F t → F t < 1 → 0 < f t

namespace TypeDist

/-- The CDF is nonnegative. -/
lemma F_nonneg (D : TypeDist) (t : Real) : 0 ≤ D.F t := by
  rw [D.F_eq t]
  exact ENNReal.toReal_nonneg

/-- The CDF is at most one. -/
lemma F_le_one (D : TypeDist) (t : Real) : D.F t ≤ 1 := by
  let : IsProbabilityMeasure D.mu := D.isProb
  rw [D.F_eq t]
  apply ENNReal.toReal_le_of_le_ofReal zero_le_one
  simpa only [ENNReal.ofReal_one] using (prob_le_one (μ := D.mu) (s := Set.Iic t))

/-- The continuous CDF is measurable. -/
lemma F_measurable (D : TypeDist) : Measurable D.F :=
  D.F_continuous.measurable

/-- The measure of a closed lower interval is the CDF as an extended nonnegative real. -/
lemma measure_Iic (D : TypeDist) (t : Real) :
    D.mu (Set.Iic t) = ENNReal.ofReal (D.F t) := by
  let : IsProbabilityMeasure D.mu := D.isProb
  rw [D.F_eq t, ENNReal.ofReal_toReal (measure_ne_top D.mu (Set.Iic t))]

/-- A distribution with a Lebesgue density assigns zero mass to each singleton. -/
lemma measure_singleton (D : TypeDist) (t : Real) : D.mu {t} = 0 := by
  rw [D.hasDensity (measurableSet_singleton t),
    setIntegral_measure_zero D.f (Real.volume_singleton (a := t)), ENNReal.ofReal_zero]

/-- The measure of a closed upper interval is one minus the CDF. -/
lemma measure_Ici (D : TypeDist) (t : Real) :
    D.mu (Set.Ici t) = ENNReal.ofReal (1 - D.F t) := by
  let : IsProbabilityMeasure D.mu := D.isProb
  have hIio : D.mu (Set.Iio t) = ENNReal.ofReal (D.F t) :=
    (measure_congr (Iio_ae_eq_Iic' (D.measure_singleton t))).trans (D.measure_Iic t)
  rw [← Set.compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, hIio,
    ENNReal.ofReal_sub 1 (D.F_nonneg t), ENNReal.ofReal_one]

/-- The CDF vanishes at nonpositive types, including the zero endpoint. -/
lemma F_eq_zero_of_nonpos (D : TypeDist) {t : Real} (ht : t ≤ 0) : D.F t = 0 := by
  have hzero : (∫ s in Set.Iio t, D.f s ∂volume) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Iio] with s hs
    exact D.f_eq_zero_of_neg s (lt_of_lt_of_le hs ht)
  have hmu : D.mu (Set.Iio t) = 0 := by
    rw [D.hasDensity measurableSet_Iio, hzero, ENNReal.ofReal_zero]
  have hIic : D.mu (Set.Iic t) = D.mu (Set.Iio t) :=
    (measure_congr (Iio_ae_eq_Iic' (D.measure_singleton t))).symm
  rw [D.F_eq t, hIic, hmu, ENNReal.toReal_zero]

/-- The density is integrable because its integral over all types is one. -/
lemma integrable_f (D : TypeDist) : Integrable D.f volume := by
  let : IsProbabilityMeasure D.mu := D.isProb
  apply integrable_of_integral_eq_one
  apply ENNReal.ofReal_eq_one.mp
  simpa only [Measure.restrict_univ, measure_univ] using
    (D.hasDensity MeasurableSet.univ).symm

end TypeDist
