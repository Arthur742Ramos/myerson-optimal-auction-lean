module

public import Myerson.MyersonLemma
public import Myerson.VirtualValue
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Myerson.Defs
public import Myerson.Dist

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace MyersonOptimalAuction

/-- Product integrand for the Fubini step of the virtual-surplus identity:
the allocation at `s` when `s` lies in the envelope interval `(0, t]`
for type `t`, and `0` otherwise. -/
@[expose] public def fubiniIntegrand (x : Real → Real) : ℝ × ℝ → ℝ :=
  fun q => (Set.Ioc 0 q.1).indicator x q.2

/-- The Fubini integrand is measurable when the allocation rule is monotone. -/
public lemma measurable_fubini (x : Real → Real) (hx : Monotone x) :
    Measurable (fubiniIntegrand x) := by
  have hx2 : Measurable (fun q : ℝ × ℝ => x q.2) := hx.measurable.comp measurable_snd
  have htri : MeasurableSet {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1} := by
    have heq : {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1}
        = Prod.snd ⁻¹' Set.Ioi 0 ∩ (Prod.fst - Prod.snd) ⁻¹' Set.Ici 0 := by
      ext q
      obtain ⟨t, s⟩ := q
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi,
        Set.mem_Ici, Pi.sub_apply]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, sub_nonneg.mpr h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, sub_nonneg.mp h2⟩
    rw [heq]
    exact (measurable_snd measurableSet_Ioi).inter
      ((measurable_fst.sub measurable_snd) measurableSet_Ici)
  have heq : fubiniIntegrand x
      = {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1}.indicator (fun q : ℝ × ℝ => x q.2) := by
    funext q
    obtain ⟨t, s⟩ := q
    have hmem : ((t, s) ∈ {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1}) = (s ∈ Set.Ioc 0 t) := by
      simp only [Set.mem_ofPred_eq, Set.mem_Ioc]
    show (Set.Ioc 0 t).indicator x s
      = ({q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1}).indicator (fun q : ℝ × ℝ => x q.2) (t, s)
    simp only [Set.indicator_apply, hmem]
  rw [heq]
  exact Measurable.indicator hx2 htri

end MyersonOptimalAuction

namespace TypeDist

/-- The type distribution is the volume measure weighted by the density. -/
public lemma mu_eq_withDensity (D : TypeDist) :
    D.mu = volume.withDensity (fun t => ENNReal.ofReal (D.f t)) := by
  apply Measure.ext
  intro s hs
  rw [D.hasDensity hs, withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal D.integrable_f.integrableOn
      (ae_of_all _ fun t => D.f_nonneg t)]

/-- Types are almost surely nonnegative under the type distribution. -/
public lemma ae_nonneg (D : TypeDist) : ∀ᵐ t ∂D.mu, 0 ≤ t := by
  rw [ae_iff]
  have hset : {t : Real | ¬ 0 ≤ t} = Set.Iio 0 := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Iio, not_le]
  rw [hset, D.hasDensity measurableSet_Iio]
  have h0 : (∫ t in Set.Iio (0 : Real), D.f t ∂volume) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
    exact D.f_eq_zero_of_neg t ht
  rw [h0, ENNReal.ofReal_zero]

/-- Integrability against the type distribution is integrability of the
density-weighted function against volume. -/
public lemma integrable_mul_density (D : TypeDist) {g : Real → Real} :
    Integrable g D.mu ↔ Integrable (fun t => g t * D.f t) volume := by
  have hmeas : Measurable (fun t => ENNReal.ofReal (D.f t)) :=
    ENNReal.measurable_ofReal.comp D.f_measurable
  rw [D.mu_eq_withDensity,
    integrable_withDensity_iff_integrable_smul' hmeas
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards with t
  rw [ENNReal.toReal_ofReal (D.f_nonneg t), smul_eq_mul, mul_comm]

/-- The Bochner integral against the type distribution is the density-weighted
volume integral. -/
public lemma integral_density (D : TypeDist) (g : Real → Real) :
    ∫ t, g t ∂D.mu = ∫ t, g t * D.f t ∂volume := by
  have hmeas : Measurable (fun t => ENNReal.ofReal (D.f t)) :=
    ENNReal.measurable_ofReal.comp D.f_measurable
  rw [D.mu_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with t
  rw [ENNReal.toReal_ofReal (D.f_nonneg t), smul_eq_mul, mul_comm]

/-- The Fubini fibers of the envelope integrand are measurable. -/
private lemma measurableSet_fiber (s : Real) :
    MeasurableSet {t : Real | s ∈ Set.Ioc 0 t} := by
  by_cases hs : 0 < s
  · have heq : {t : Real | s ∈ Set.Ioc 0 t} = Set.Ici s := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_Ioc, Set.mem_Ici]
      exact ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩
    rw [heq]
    exact measurableSet_Ici
  · have heq : {t : Real | s ∈ Set.Ioc 0 t} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, -⟩
      exact absurd h1 hs
    rw [heq]
    exact MeasurableSet.empty

/-- Fubini/Tonelli rewrite of the expected envelope integral: the expectation
(over the type distribution) of the allocation integral from the reference
type zero equals the volume integral of the allocation weighted by the
survival probability. -/
public lemma tonelli_allocation (x : Real → Real) (D : TypeDist)
    (hx : Monotone x)
    (_hIntG : Integrable (fun t => ∫ s in (0:Real)..t, x s) D.mu)
    (hInt : Integrable (fun s => x s * (1 - D.F s)) volume) :
    ∫ t, (∫ s in (0:Real)..t, x s) ∂D.mu
      = ∫ s in Set.Ici (0:Real), x s * (1 - D.F s) ∂volume := by
  let : IsProbabilityMeasure D.mu := D.isProb
  have hFmeas := MyersonOptimalAuction.measurable_fubini x hx
  -- The lintegral inner integral over each fiber.
  have h1 : ∀ s : Real, (∫⁻ t, (‖MyersonOptimalAuction.fubiniIntegrand x (t, s)‖ₑ) ∂D.mu)
      = ‖x s‖ₑ * (if 0 < s then ENNReal.ofReal (1 - D.F s) else 0) := by
    intro s
    have heq : (fun t => ‖MyersonOptimalAuction.fubiniIntegrand x (t, s)‖ₑ)
        = ({t | s ∈ Set.Ioc 0 t}).indicator (fun _ => ‖x s‖ₑ) := by
      funext t
      show ‖(Set.Ioc 0 t).indicator x s‖ₑ
        = ({t | s ∈ Set.Ioc 0 t}).indicator (fun _ => ‖x s‖ₑ) t
      by_cases h : s ∈ Set.Ioc 0 t
      · have hm : t ∈ {t | s ∈ Set.Ioc 0 t} := h
        rw [Set.indicator_of_mem h, Set.indicator_of_mem hm]
      · have hm : t ∉ {t | s ∈ Set.Ioc 0 t} := h
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hm]
        simp
    rw [heq, lintegral_indicator (measurableSet_fiber s), setLIntegral_const]
    by_cases hs : 0 < s
    · have hEs : {t : Real | s ∈ Set.Ioc 0 t} = Set.Ici s := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_Ioc, Set.mem_Ici]
        exact ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩
      rw [ite_eq_left hs, hEs, D.measure_Ici]
    · have hEs : {t : Real | s ∈ Set.Ioc 0 t} = ∅ := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, -⟩
        exact absurd h1 hs
      rw [ite_eq_right hs, hEs, measure_empty]
  -- The product integrand is integrable: bound the iterated lintegral.
  have hle : (∫⁻ s, (∫⁻ t, (‖MyersonOptimalAuction.fubiniIntegrand x (t, s)‖ₑ) ∂D.mu) ∂volume)
      ≤ ∫⁻ s, (‖x s * (1 - D.F s)‖ₑ) ∂volume := by
    apply lintegral_mono_ae
    filter_upwards with s
    rw [h1 s]
    by_cases hs : 0 < s
    · rw [ite_eq_left hs, enorm_mul, Real.enorm_of_nonneg (sub_nonneg.mpr (D.F_le_one s))]
    · rw [ite_eq_right hs, mul_zero]
      exact zero_le
  -- The product lintegral is finite: rewrite via Tonelli into the iterated bound.
  have hHfin : ∫⁻ q, (‖MyersonOptimalAuction.fubiniIntegrand x q‖ₑ) ∂(D.mu.prod volume) < ∞ := by
    have e := lintegral_prod_symm (μ := D.mu) (ν := volume)
      (fun q => ‖MyersonOptimalAuction.fubiniIntegrand x q‖ₑ) hFmeas.aemeasurable.enorm
    rw [e]
    exact lt_of_le_of_lt hle hInt.hasFiniteIntegral
  have hH : Integrable (MyersonOptimalAuction.fubiniIntegrand x) (D.mu.prod volume) :=
    ⟨hFmeas.aestronglyMeasurable, hHfin⟩
  have hH' : Integrable (Function.uncurry fun t s => MyersonOptimalAuction.fubiniIntegrand x (t, s))
      (D.mu.prod volume) := hH
  have hswap := integral_integral_swap (μ := D.mu) (ν := volume)
    (f := fun t s => MyersonOptimalAuction.fubiniIntegrand x (t, s)) hH'
  -- Left-hand side: the inner volume integral is the envelope integral.
  have hLHS : (∫ t, ∫ s, MyersonOptimalAuction.fubiniIntegrand x (t, s) ∂volume ∂D.mu)
      = ∫ t, (∫ s in (0:Real)..t, x s) ∂D.mu := by
    apply integral_congr_ae
    filter_upwards [D.ae_nonneg] with t ht
    show (∫ s, MyersonOptimalAuction.fubiniIntegrand x (t, s) ∂volume)
      = ∫ s in (0:Real)..t, x s
    show (∫ s, (Set.Ioc 0 t).indicator x s ∂volume) = _
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le ht]
  -- The inner Bochner integral over each fiber.
  have hinnerB : ∀ s : Real, (∫ t, MyersonOptimalAuction.fubiniIntegrand x (t, s) ∂D.mu)
      = (if 0 < s then (1 - D.F s) * x s else 0) := by
    intro s
    have heq : (fun t => MyersonOptimalAuction.fubiniIntegrand x (t, s))
        = ({t | s ∈ Set.Ioc 0 t}).indicator (fun _ => x s) := by
      funext t
      show (Set.Ioc 0 t).indicator x s
        = ({t | s ∈ Set.Ioc 0 t}).indicator (fun _ => x s) t
      by_cases h : s ∈ Set.Ioc 0 t
      · rw [Set.indicator_of_mem h]
        have hm : t ∈ {t | s ∈ Set.Ioc 0 t} := h
        rw [Set.indicator_of_mem hm]
      · rw [Set.indicator_of_notMem h]
        have hm : t ∉ {t | s ∈ Set.Ioc 0 t} := h
        rw [Set.indicator_of_notMem hm]
    rw [heq, integral_indicator (measurableSet_fiber s), setIntegral_const]
    by_cases hs : 0 < s
    · have hEs : {t : Real | s ∈ Set.Ioc 0 t} = Set.Ici s := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_Ioc, Set.mem_Ici]
        exact ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩
      rw [ite_eq_left hs, hEs]
      show (D.mu (Set.Ici s)).toReal • x s = (1 - D.F s) * x s
      rw [D.measure_Ici, ENNReal.toReal_ofReal (sub_nonneg.mpr (D.F_le_one s)), smul_eq_mul]
    · have hEs : {t : Real | s ∈ Set.Ioc 0 t} = ∅ := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, -⟩
        exact absurd h1 hs
      rw [ite_eq_right hs, hEs]
      simp
  -- Right-hand side: the fiber integrals assemble into the survival-weighted integral.
  have hRHS : (∫ s, ∫ t, MyersonOptimalAuction.fubiniIntegrand x (t, s) ∂D.mu ∂volume)
      = ∫ s in Set.Ici (0:Real), x s * (1 - D.F s) ∂volume := by
    rw [← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    have hnull : ∀ᵐ s ∂(volume : Measure Real), s ≠ 0 := by
      rw [ae_iff]
      have hset : {s : Real | ¬ s ≠ 0} = {0} := by
        ext s
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, not_ne_iff]
      rw [hset]
      exact Real.volume_singleton
    filter_upwards [hnull] with s hs
    rw [hinnerB s]
    by_cases hpos : 0 < s
    · have hmem : s ∈ Set.Ici (0:Real) := hpos.le
      rw [ite_eq_left hpos, Set.indicator_of_mem hmem]
      ring
    · have hnotmem : s ∉ Set.Ici (0:Real) := by
        intro hmem
        exact hpos (lt_of_le_of_ne (Set.mem_Ici.mp hmem) (Ne.symm hs))
      rw [ite_eq_right hpos, Set.indicator_of_notMem hnotmem]
  calc (∫ t, (∫ s in (0:Real)..t, x s) ∂D.mu)
      = (∫ t, ∫ s, MyersonOptimalAuction.fubiniIntegrand x (t, s) ∂volume ∂D.mu) :=
        hLHS.symm
    _ = (∫ s, ∫ t, MyersonOptimalAuction.fubiniIntegrand x (t, s) ∂D.mu ∂volume) := hswap
    _ = ∫ s in Set.Ici (0:Real), x s * (1 - D.F s) ∂volume := hRHS

end TypeDist

namespace MyersonOptimalAuction

/-- The virtual-surplus identity: under BIC, the expected payment equals the
expected virtual surplus minus the interim utility of the reference type zero.

The integrability hypotheses are load-bearing: without them Lean's totalized
Bochner integral makes the expectation equality vacuous. The support
hypothesis `hsupp` (the distribution puts positive mass above every positive
type) is sharp: without it the identity is false. For example, a constant unit
allocation with zero payments under a uniform[1,2] prior satisfies BIC and all
integrability hypotheses, yet has expected payment `0 ≠ 1` = expected virtual
surplus minus reference utility. -/
public theorem virtualSurplusIdentity (x p : Real → Real) (D : TypeDist)
    (hBIC : BIC x p)
    (hsupp : ∀ t : Real, 0 < t → 0 < D.F t)
    (_hInt_p : Integrable p D.mu)
    (hInt_tx : Integrable (fun t => t * x t) D.mu)
    (hIntG : Integrable (fun t => ∫ s in (0:Real)..t, x s) D.mu)
    (hInt_xw : Integrable (fun s => x s * (1 - D.F s)) volume)
    (_hInt_psix : Integrable (fun t => virtualValue D.F D.f t * x t) D.mu) :
    expectedPayment p D = expectedVirtualSurplus x D - interimUtility x p 0 := by
  have hxmono := x_monotone_of_BIC x p hBIC
  have hpay := payment_formula_of_BIC x p hBIC
  let : IsProbabilityMeasure D.mu := D.isProb
  -- The reference utility integrates to itself against a probability measure.
  have hU0 : (∫ _ : Real, interimUtility x p 0 ∂D.mu) = interimUtility x p 0 := by
    rw [integral_const, show D.mu.real Set.univ = 1 from by
      show (D.mu Set.univ).toReal = 1
      rw [D.isProb.measure_univ, ENNReal.toReal_one]]
    exact one_smul _ _
  -- Step 1: split the expected payment via the envelope payment formula.
  have hsplit : (∫ t, p t ∂D.mu)
      = (∫ t, t * x t ∂D.mu) - (∫ t, (∫ s in (0:Real)..t, x s) ∂D.mu)
        - interimUtility x p 0 := by
    have h1 : Integrable (fun t => t * x t - (∫ s in (0:Real)..t, x s)) D.mu :=
      hInt_tx.sub hIntG
    have h2 : Integrable (fun _ : Real => interimUtility x p 0) D.mu := integrable_const _
    calc (∫ t, p t ∂D.mu)
        = ∫ t, ((t * x t - (∫ s in (0:Real)..t, x s)) - interimUtility x p 0) ∂D.mu := by
          apply integral_congr_ae
          filter_upwards with t
          rw [hpay t]
          ring
      _ = (∫ t, (t * x t - (∫ s in (0:Real)..t, x s)) ∂D.mu)
          - (∫ _ : Real, interimUtility x p 0 ∂D.mu) := by
          have e := integral_sub h1 h2
          rw [show (∫ t, ((t * x t - (∫ s in (0:Real)..t, x s))
              - interimUtility x p 0) ∂D.mu)
            = (∫ t, (t * x t - (∫ s in (0:Real)..t, x s)) ∂D.mu)
              - (∫ _ : Real, interimUtility x p 0 ∂D.mu)
            from e, hU0]
      _ = ((∫ t, t * x t ∂D.mu) - (∫ t, (∫ s in (0:Real)..t, x s) ∂D.mu))
          - interimUtility x p 0 := by
          have e := integral_sub hInt_tx hIntG
          rw [show (∫ t, (t * x t - (∫ s in (0:Real)..t, x s)) ∂D.mu)
            = (∫ t, t * x t ∂D.mu) - (∫ t, (∫ s in (0:Real)..t, x s) ∂D.mu) from e,
            hU0]
  -- Steps 2-4: move to density-weighted volume integrals and cancel.
  have hA : (∫ t, t * x t ∂D.mu) = ∫ t, t * x t * D.f t ∂volume :=
    D.integral_density _
  have hB : (∫ t, (∫ s in (0:Real)..t, x s) ∂D.mu)
      = ∫ s in Set.Ici (0:Real), x s * (1 - D.F s) ∂volume :=
    D.tonelli_allocation x hxmono hIntG hInt_xw
  have hC : (∫ t, virtualValue D.F D.f t * x t ∂D.mu)
      = ∫ t, virtualValue D.F D.f t * x t * D.f t ∂volume :=
    D.integral_density _
  rw [expectedPayment_apply, expectedVirtualSurplus_apply, hsplit, hA, hB, hC]
  -- The integrands combine: the Tonelli term cancels the hazard-rate part of ψ.
  have key : (∫ t, t * x t * D.f t ∂volume)
        - (∫ s in Set.Ici (0:Real), x s * (1 - D.F s) ∂volume)
      = ∫ t, virtualValue D.F D.f t * x t * D.f t ∂volume := by
    rw [← integral_indicator measurableSet_Ici]
    have hIci : MeasurableSet (Set.Ici (0:Real)) := measurableSet_Ici
    have hf1 : Integrable (fun t => t * x t * D.f t) volume :=
      D.integrable_mul_density.mp hInt_tx
    have hf2 : Integrable ((Set.Ici (0:Real)).indicator (fun s => x s * (1 - D.F s))) volume :=
      Integrable.indicator hInt_xw hIci
    have hsub := (integral_sub hf1 hf2).symm
    rw [hsub]
    apply integral_congr_ae
    have hnull : ∀ᵐ t ∂(volume : Measure Real), t ≠ 0 := by
      rw [ae_iff]
      have hset : {t : Real | ¬ t ≠ 0} = {0} := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, not_ne_iff]
      rw [hset]
      exact Real.volume_singleton
    filter_upwards [hnull] with t ht
    show t * x t * D.f t - (Set.Ici (0:Real)).indicator (fun s => x s * (1 - D.F s)) t
      = virtualValue D.F D.f t * x t * D.f t
    by_cases hneg : t < 0
    · -- Negative types: the density vanishes and so does the indicator.
      have hft : D.f t = 0 := D.f_eq_zero_of_neg t hneg
      have hind : (Set.Ici (0:Real)).indicator (fun s => x s * (1 - D.F s)) t = 0 := by
        apply Set.indicator_of_notMem
        simp only [Set.mem_Ici, not_le]
        exact hneg
      rw [hft, hind]
      ring
    · by_cases hpos : 0 < t
      · -- Positive types: the indicator is live; cancel the density.
        have hind : (Set.Ici (0:Real)).indicator (fun s => x s * (1 - D.F s)) t
            = x t * (1 - D.F t) :=
          Set.indicator_of_mem hpos.le _
        rw [hind]
        by_cases hf : D.f t = 0
        · -- Zero density at a positive type forces `F t = 1` via `hsupp`.
          have hF1 : D.F t = 1 := by
            have hposF : 0 < D.F t := hsupp t hpos
            rcases eq_or_lt_of_le (D.F_le_one t) with h | h
            · exact h
            · exfalso
              have hposf := D.pos_of_interior t hposF h
              rw [hf] at hposf
              exact lt_irrefl 0 hposf
          rw [hf, hF1]
          ring
        · have hvv := MyersonOptimalAuction.virtualValue_mul_density D.F D.f t hf
          calc t * x t * D.f t - x t * (1 - D.F t)
              = x t * (t * D.f t - (1 - D.F t)) := by ring
            _ = x t * (virtualValue D.F D.f t * D.f t) := by rw [← hvv]
            _ = virtualValue D.F D.f t * x t * D.f t := by ring
      · exfalso
        exact ht (le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg))
  rw [key]

end MyersonOptimalAuction
