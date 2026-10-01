module

public import Myerson.Defs
public import Myerson.Dist
public import Myerson.VirtualValue
public import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory

noncomputable section

namespace MyersonOptimalAuction

/-
Witness that the repaired hypotheses are jointly satisfiable.

The uniform distribution on [0,1] is a `TypeDist` that is regular (virtual
values monotone on nonnegative types), has full support near zero
(`hsupp`), and has integrable identity and virtual-value functions. This
kills the vacuity objection: the optimal-auction theorem's hypotheses are
jointly satisfiable.
-/

/-- The uniform distribution on [0,1] as a `TypeDist`. The CDF is given in
closed form; the density is the indicator of [0,1]. -/
@[expose] public noncomputable def uniform01 : TypeDist where
  mu := volume.restrict (Set.Icc (0 : Real) 1)
  F := fun t => max 0 (min 1 t)
  f := Set.indicator (Set.Icc (0 : Real) 1) 1
  isProb := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ (Set.Icc (0 : Real) 1), Real.volume_Icc]
    norm_num
  F_continuous := continuous_const.max (continuous_const.min continuous_id)
  F_monotone := by
    intro a b hab
    show max (0 : Real) (min 1 a) ≤ max 0 (min 1 b)
    exact max_le_max le_rfl (min_le_min le_rfl hab)
  f_measurable := measurable_const.indicator measurableSet_Icc
  f_nonneg := by
    intro t
    by_cases h : t ∈ Set.Icc (0 : Real) 1
    · rw [Set.indicator_of_mem h, Pi.one_apply]; exact zero_le_one
    · rw [Set.indicator_of_notMem h]
  F_eq := by
    intro t
    show max (0 : Real) (min 1 t) = (volume.restrict (Set.Icc 0 1) (Set.Iic t)).toReal
    rw [Measure.restrict_apply measurableSet_Iic]
    have hinter : Set.Iic t ∩ Set.Icc (0 : Real) 1 = Set.Icc 0 (min t 1) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h2, le_min h1 h3⟩
      · rintro ⟨h2, h3⟩
        exact ⟨(le_min_iff.mp h3).1, h2, (le_min_iff.mp h3).2⟩
    rw [hinter, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal',
      max_comm (min t 1) 0, min_comm t 1]
  hasDensity := by
    intro s hs
    show volume.restrict (Set.Icc (0 : Real) 1) s =
      ENNReal.ofReal (∫ t in s, Set.indicator (Set.Icc 0 1) 1 t ∂volume)
    rw [Measure.restrict_apply hs, setIntegral_indicator measurableSet_Icc]
    simp only [Pi.one_apply]
    rw [setIntegral_const, smul_eq_mul, mul_one]
    have hfin : volume (s ∩ Set.Icc (0 : Real) 1) < ⊤ :=
      calc volume (s ∩ Set.Icc (0 : Real) 1)
          ≤ volume (Set.Icc (0 : Real) 1) := measure_mono Set.inter_subset_right
        _ = ENNReal.ofReal 1 := by rw [Real.volume_Icc]; norm_num
        _ < ⊤ := ENNReal.ofReal_lt_top
    exact (ENNReal.ofReal_toReal (ne_of_lt hfin)).symm
  f_eq_zero_of_neg := by
    intro t ht
    show Set.indicator (Set.Icc (0 : Real) 1) 1 t = 0
    apply Set.indicator_of_notMem
    intro hmem
    rw [Set.mem_Icc] at hmem
    linarith
  pos_of_interior := by
    intro t h0 h1
    -- Here h0 : 0 < max 0 (min 1 t) and h1 : max 0 (min 1 t) < 1.
    have ht0 : 0 < t := by
      by_contra hc
      have hle : t ≤ 0 := le_of_not_gt hc
      have hmax : max (0 : Real) (min 1 t) = 0 :=
        max_eq_left (min_le_of_right_le (by linarith))
      rw [hmax] at h0
      exact lt_irrefl 0 h0
    have ht1 : t < 1 := by
      by_contra hc
      have hge : 1 ≤ t := le_of_not_gt hc
      have hmax : max (0 : Real) (min 1 t) = 1 := by
        rw [min_eq_left hge, max_eq_right (by norm_num)]
      rw [hmax] at h1
      exact lt_irrefl 1 h1
    have hmem : t ∈ Set.Icc (0 : Real) 1 := by
      rw [Set.mem_Icc]; exact ⟨le_of_lt ht0, le_of_lt ht1⟩
    show 0 < Set.indicator (Set.Icc (0 : Real) 1) 1 t
    rw [Set.indicator_of_mem hmem, Pi.one_apply]
    exact one_pos

/-- The CDF of `uniform01` in closed form. -/
public theorem uniform01_F (t : Real) : uniform01.F t = max 0 (min 1 t) := rfl

/-- The density of `uniform01` is 1 on [0,1]. -/
public theorem uniform01_f_of_mem {t : Real} (h : t ∈ Set.Icc (0 : Real) 1) :
    uniform01.f t = 1 := by
  show Set.indicator (Set.Icc (0 : Real) 1) 1 t = 1
  rw [Set.indicator_of_mem h, Pi.one_apply]

/-- The density of `uniform01` is 0 off [0,1]. -/
public theorem uniform01_f_of_notMem {t : Real} (h : t ∉ Set.Icc (0 : Real) 1) :
    uniform01.f t = 0 := by
  show Set.indicator (Set.Icc (0 : Real) 1) 1 t = 0
  exact Set.indicator_of_notMem h 1

/-- Virtual values of `uniform01` on nonnegative types: `2t - 1` on [0,1]
(the usual uniform virtual value) and `t` above 1 (where the density
vanishes, so the totalized inverse hazard rate is zero). In particular
`vv(0) = -1`: the virtual value is negative at zero, which is exactly what
global monotonicity could not tolerate. -/
public theorem uniform01_vv {t : Real} (ht : 0 ≤ t) :
    virtualValue uniform01.F uniform01.f t = min (2 * t - 1) t := by
  by_cases h1 : t ≤ 1
  · have hf : uniform01.f t = 1 :=
      uniform01_f_of_mem (by rw [Set.mem_Icc]; exact ⟨ht, h1⟩)
    have hF : uniform01.F t = t := by
      rw [uniform01_F, min_eq_right h1, max_eq_right ht]
    rw [virtualValue_eq, hf, hF, div_one,
      min_eq_left (by linarith : 2 * t - 1 ≤ t)]
    ring
  · have h1' : 1 < t := lt_of_not_ge h1
    have hf : uniform01.f t = 0 := by
      apply uniform01_f_of_notMem
      rw [Set.mem_Icc]
      exact fun h => absurd h.2 (not_le.mpr h1')
    have hF : uniform01.F t = 1 := by
      rw [uniform01_F, min_eq_left (le_of_lt h1'), max_eq_right (by norm_num)]
    rw [virtualValue_eq, hf, hF, div_zero, sub_zero,
      min_eq_right (by linarith : t ≤ 2 * t - 1)]

/-- `uniform01` is regular: virtual values are monotone on nonnegative types. -/
public theorem uniform01_regular : Regular (fun _ : Fin 1 => uniform01) := by
  intro i a ha b hb hab
  rw [Set.mem_Ici] at ha hb
  show virtualValue uniform01.F uniform01.f a ≤ virtualValue uniform01.F uniform01.f b
  rw [uniform01_vv ha, uniform01_vv hb]
  exact min_le_min (by linarith) hab

/-- `uniform01` satisfies the support hypothesis: every positive type sees
positive mass in `(0, t]`. -/
public theorem uniform01_hsupp : ∀ t : Real, 0 < t → 0 < uniform01.F t := by
  intro t ht
  rw [uniform01_F, lt_max_iff, lt_min_iff]
  exact Or.inr ⟨one_pos, ht⟩

/-- The identity is integrable against `uniform01.mu`. -/
public theorem uniform01_integrable_id :
    Integrable (fun t : Real => t) uniform01.mu := by
  haveI := uniform01.isProb
  apply Integrable.of_bound aestronglyMeasurable_id 1
  have hae : ∀ᵐ t ∂uniform01.mu, t ∈ Set.Icc (0 : Real) 1 :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [hae] with t ht
  rw [Set.mem_Icc] at ht
  simp only [id_eq]
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Virtual values are integrable against `uniform01.mu`. -/
public theorem uniform01_integrable_vv :
    Integrable (fun t => virtualValue uniform01.F uniform01.f t) uniform01.mu := by
  haveI := uniform01.isProb
  apply Integrable.of_bound uniform01.measurable_virtualValue.aestronglyMeasurable 1
  have hae : ∀ᵐ t ∂uniform01.mu, t ∈ Set.Icc (0 : Real) 1 :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [hae] with t ht
  rw [Set.mem_Icc] at ht
  rw [uniform01_vv ht.1, Real.norm_eq_abs, abs_le]
  refine ⟨le_min (by linarith) (by linarith), ?_⟩
  exact (min_le_right _ _).trans (by linarith)

/-- The repaired hypotheses are jointly satisfiable: `uniform01` is a regular
prior with full support near zero and integrable identity and virtual-value
functions. The optimal-auction theorem is not vacuous. -/
public theorem uniform01_qualifies :
    Regular (fun _ : Fin 1 => uniform01)
      ∧ (∀ t : Real, 0 < t → 0 < uniform01.F t)
      ∧ Integrable (fun t : Real => t) uniform01.mu
      ∧ Integrable (fun t => virtualValue uniform01.F uniform01.f t) uniform01.mu :=
  ⟨uniform01_regular, uniform01_hsupp, uniform01_integrable_id, uniform01_integrable_vv⟩

end MyersonOptimalAuction
