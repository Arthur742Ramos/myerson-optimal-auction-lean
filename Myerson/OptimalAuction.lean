import Myerson.FubiniCoord
import Myerson.MyersonLemma
import Myerson.VirtualSurplus
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Order.Lattice

open MeasureTheory
open MyersonOptimalAuction

noncomputable section

namespace Myerson

variable {n : Nat} (D : Fin n → TypeDist) (hn : 0 < n)

/-- The largest virtual value at a type profile. -/
noncomputable def maxVirt (t : Fin n → Real) : Real :=
  Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (fun i => virtualValue (D i).F (D i).f (t i))

/-- Bidders attaining the largest virtual value. -/
noncomputable def attainers (t : Fin n → Real) : Finset (Fin n) :=
  Finset.univ.filter
    (fun i => virtualValue (D i).F (D i).f (t i) = maxVirt D hn t)

lemma attainers_nonempty (t : Fin n → Real) : (attainers D hn t).Nonempty := by
  classical
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Fin n)))
    (H := ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
    (fun i => virtualValue (D i).F (D i).f (t i))
  exact ⟨j, Finset.mem_filter.mpr ⟨hj, heq.symm⟩⟩

/-- Ties for largest virtual value are broken by the least bidder index. -/
noncomputable def winner (t : Fin n → Real) : Fin n :=
  (attainers D hn t).min' (attainers_nonempty D hn t)

lemma winner_mem (t : Fin n → Real) : winner D hn t ∈ attainers D hn t :=
  Finset.min'_mem _ _

lemma winner_eq_iff (t : Fin n → Real) (i : Fin n) :
    winner D hn t = i ↔
      virtualValue (D i).F (D i).f (t i) = maxVirt D hn t ∧
        ∀ j, virtualValue (D j).F (D j).f (t j) = maxVirt D hn t → i ≤ j := by
  classical
  constructor
  · intro hwin
    have hatt := (Finset.mem_filter.mp (winner_mem D hn t)).2
    rw [hwin] at hatt
    refine ⟨hatt, ?_⟩
    intro j hj
    have hjmem : j ∈ attainers D hn t :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    have hle : winner D hn t ≤ j := Finset.min'_le _ j hjmem
    rwa [hwin] at hle
  · rintro ⟨hatt, hleast⟩
    have himem : i ∈ attainers D hn t :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hatt⟩
    exact le_antisymm (Finset.min'_le _ i himem)
      (hleast _ (Finset.mem_filter.mp (winner_mem D hn t)).2)

/-- Allocate to the selected bidder exactly when the largest virtual value is positive. -/
noncomputable def optAlloc (i : Fin n) : (Fin n → Real) → Real :=
  {t : Fin n → Real | 0 < maxVirt D hn t ∧ winner D hn t = i}.indicator 1

noncomputable def optInterim (i : Fin n) : Real → Real :=
  interimAlloc D (optAlloc D hn) i

/-- Envelope payments normalized to utility zero at type zero. -/
noncomputable def optPayment (i : Fin n) (t : Real) : Real :=
  t * optInterim D hn i t - ∫ s in (0 : Real)..t, optInterim D hn i s

include hn in
lemma virt_nonpos_of_nonpos (i : Fin n) {s : Real} (hs : s ≤ 0) :
    virtualValue (D i).F (D i).f s ≤ 0 := by
  rcases lt_or_eq_of_le hs with hneg | rfl
  · have hF := (D i).F_eq_zero_of_nonpos (le_of_lt hneg)
    have hf := (D i).f_eq_zero_of_neg s hneg
    show s - (1 - (D i).F s) / (D i).f s ≤ 0
    rw [hF, hf, div_zero, sub_zero]
    exact le_of_lt hneg
  · have hF := (D i).F_eq_zero_of_nonpos (t := 0) le_rfl
    show (0 : Real) - (1 - (D i).F 0) / (D i).f 0 ≤ 0
    rw [hF, sub_zero, zero_sub]
    exact neg_nonpos.mpr (one_div_nonneg.mpr ((D i).f_nonneg 0))

lemma measurable_maxVirt : Measurable (maxVirt D hn) := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hm : Measurable (Finset.univ.sup' hne
      (fun i => fun t : Fin n → Real => virtualValue (D i).F (D i).f (t i))) :=
    Finset.measurable_sup' hne
      (fun i _ => (D i).measurable_virtualValue.comp (measurable_pi_apply i))
  have heq : Finset.univ.sup' hne
      (fun i => fun t : Fin n → Real => virtualValue (D i).F (D i).f (t i))
      = maxVirt D hn := by
    funext t
    exact Finset.sup'_apply hne _ t
  rwa [heq] at hm

lemma measurableSet_winner_eq (i : Fin n) :
    MeasurableSet {t : Fin n → Real | winner D hn t = i} := by
  classical
  have heq : {t : Fin n → Real | winner D hn t = i} =
      {t : Fin n → Real |
        virtualValue (D i).F (D i).f (t i) = maxVirt D hn t} ∩
      ⋂ j ∈ (↑(Finset.univ.filter (fun j : Fin n => j < i)) : Set (Fin n)),
        {t : Fin n → Real |
          virtualValue (D j).F (D j).f (t j) ≠ maxVirt D hn t} := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hw
      obtain ⟨hatt, hleast⟩ := (winner_eq_iff D hn t i).mp hw
      refine ⟨hatt, ?_⟩
      intro j hj hjatt
      have hjlt : j < i := (Finset.mem_filter.mp hj).2
      exact (not_le_of_gt hjlt) (hleast j hjatt)
    · rintro ⟨hatt, hsmall⟩
      apply (winner_eq_iff D hn t i).mpr
      refine ⟨hatt, ?_⟩
      intro j hjatt
      by_contra hle
      have hjlt : j < i := lt_of_not_ge hle
      exact hsmall j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjlt⟩) hjatt
  rw [heq]
  refine (measurableSet_eq_fun
    ((D i).measurable_virtualValue.comp (measurable_pi_apply i))
    (measurable_maxVirt D hn)).inter ?_
  apply (Finset.finite_toSet _).measurableSet_biInter
  intro j _
  exact (measurableSet_eq_fun
    ((D j).measurable_virtualValue.comp (measurable_pi_apply j))
    (measurable_maxVirt D hn)).compl

lemma measurable_optAlloc (i : Fin n) : Measurable (optAlloc D hn i) := by
  classical
  unfold optAlloc
  exact measurable_const.indicator
    ((measurableSet_lt measurable_const (measurable_maxVirt D hn)).inter
      (measurableSet_winner_eq D hn i))

lemma measurable_optInterim (i : Fin n) : Measurable (optInterim D hn i) :=
  measurable_interimAlloc D i (optAlloc D hn) (measurable_optAlloc D hn i)

lemma optAlloc_nonneg (i : Fin n) (t : Fin n → Real) : 0 ≤ optAlloc D hn i t := by
  classical
  unfold optAlloc
  by_cases h : t ∈ {t : Fin n → Real | 0 < maxVirt D hn t ∧ winner D hn t = i}
  · simpa only [Set.indicator_of_mem h, Pi.one_apply] using (zero_le_one : (0 : Real) ≤ 1)
  · simpa only [Set.indicator_of_notMem h] using (le_refl (0 : Real))

lemma optAlloc_le_one (i : Fin n) (t : Fin n → Real) : optAlloc D hn i t ≤ 1 := by
  classical
  unfold optAlloc
  by_cases h : t ∈ {t : Fin n → Real | 0 < maxVirt D hn t ∧ winner D hn t = i}
  · simpa only [Set.indicator_of_mem h, Pi.one_apply] using (le_refl (1 : Real))
  · simpa only [Set.indicator_of_notMem h] using (zero_le_one : (0 : Real) ≤ 1)

private lemma optAlloc_norm_le_one (i : Fin n) (t : Fin n → Real) :
    ‖optAlloc D hn i t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [optAlloc_nonneg D hn i t], optAlloc_le_one D hn i t⟩

lemma optInterim_nonneg (i : Fin n) (s : Real) : 0 ≤ optInterim D hn i s :=
  interimAlloc_nonneg D i (optAlloc D hn) (fun i t => optAlloc_nonneg D hn i t) s

lemma optInterim_le_one (i : Fin n) (s : Real) : optInterim D hn i s ≤ 1 :=
  interimAlloc_le_one D i (optAlloc D hn) (fun i => measurable_optAlloc D hn i)
    (fun i t => optAlloc_norm_le_one D hn i t) s

lemma optInterim_norm_le_one (i : Fin n) (t : Real) : ‖optInterim D hn i t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [optInterim_nonneg D hn i t], optInterim_le_one D hn i t⟩

private lemma virt_le_maxVirt (i : Fin n) (t : Fin n → Real) :
    virtualValue (D i).F (D i).f (t i) ≤ maxVirt D hn t :=
  Finset.le_sup' (fun j => virtualValue (D j).F (D j).f (t j)) (Finset.mem_univ i)

lemma virtSurplus_le (X : Fin n → (Fin n → Real) → Real)
    (hXnn : ∀ i t, 0 ≤ X i t) (hXsum : ∀ t, ∑ i, X i t ≤ 1)
    (t : Fin n → Real) :
    ∑ i, virtualValue (D i).F (D i).f (t i) * X i t ≤ max 0 (maxVirt D hn t) := by
  classical
  by_cases hM : 0 < maxVirt D hn t
  · calc
      ∑ i, virtualValue (D i).F (D i).f (t i) * X i t
          ≤ ∑ i, maxVirt D hn t * X i t :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (virt_le_maxVirt D hn i t) (hXnn i t)
      _ = maxVirt D hn t * ∑ i, X i t := (Finset.mul_sum _ _ _).symm
      _ ≤ maxVirt D hn t * 1 := mul_le_mul_of_nonneg_left (hXsum t) hM.le
      _ ≤ max 0 (maxVirt D hn t) := by
        rw [mul_one]
        exact le_max_right _ _
  · have hMle : maxVirt D hn t ≤ 0 := le_of_not_gt hM
    exact (Finset.sum_nonpos fun i _ =>
      mul_nonpos_of_nonpos_of_nonneg ((virt_le_maxVirt D hn i t).trans hMle)
        (hXnn i t)).trans (le_max_left _ _)

lemma virtSurplus_opt (t : Fin n → Real) :
    ∑ i, virtualValue (D i).F (D i).f (t i) * optAlloc D hn i t =
      max 0 (maxVirt D hn t) := by
  classical
  by_cases hM : 0 < maxVirt D hn t
  · let w := winner D hn t
    have hatt : virtualValue (D w).F (D w).f (t w) = maxVirt D hn t :=
      (Finset.mem_filter.mp (winner_mem D hn t)).2
    have halloc : ∀ i, optAlloc D hn i t = if i = w then 1 else 0 := by
      intro i
      unfold optAlloc
      by_cases hi : i = w
      · subst i
        simp only [Set.indicator_of_mem (show t ∈
          {t : Fin n → Real | 0 < maxVirt D hn t ∧ winner D hn t = w}
          from ⟨hM, rfl⟩), Pi.one_apply]
        simp
      · rw [Set.indicator_of_notMem (show t ∉
          {t : Fin n → Real | 0 < maxVirt D hn t ∧ winner D hn t = i} from by
            rintro ⟨_, hwi⟩
            exact hi hwi.symm), ite_eq_right hi]
    rw [max_eq_right hM.le]
    calc
      ∑ i, virtualValue (D i).F (D i).f (t i) * optAlloc D hn i t
          = virtualValue (D w).F (D w).f (t w) * optAlloc D hn w t := by
        apply Finset.sum_eq_single w
        · intro i _ hi
          rw [halloc i, ite_eq_right hi, mul_zero]
        · intro hw
          exact (hw (Finset.mem_univ w)).elim
      _ = maxVirt D hn t := by rw [halloc w, ite_eq_left rfl, mul_one, hatt]
  · have hMle : maxVirt D hn t ≤ 0 := le_of_not_gt hM
    have halloc : ∀ i, optAlloc D hn i t = 0 := by
      intro i
      unfold optAlloc
      exact Set.indicator_of_notMem (by
        rintro ⟨hpos, _⟩
        exact (not_lt.mpr hMle) hpos) _
    simp only [halloc, mul_zero, Finset.sum_const_zero, max_eq_left hMle]

lemma optAlloc_mono_update (i : Fin n) (u : Fin n → Real) {s s' : Real}
    (hle : s ≤ s') (hreg : Monotone fun t => virtualValue (D i).F (D i).f t) :
    optAlloc D hn i (Function.update u i s) ≤ optAlloc D hn i (Function.update u i s') := by
  classical
  by_cases h1 : optAlloc D hn i (Function.update u i s) = 1
  · have hmem : 0 < maxVirt D hn (Function.update u i s) ∧
        winner D hn (Function.update u i s) = i := by
      by_contra hnot
      have hzero : optAlloc D hn i (Function.update u i s) = 0 :=
        Set.indicator_of_notMem (show (Function.update u i s) ∉
          {t : Fin n → Real | 0 < maxVirt D hn t ∧ winner D hn t = i} from hnot) _
      rw [hzero] at h1
      exact zero_ne_one h1
    obtain ⟨hMpos, hwin⟩ := hmem
    obtain ⟨hatt0, hleast⟩ := (winner_eq_iff D hn (Function.update u i s) i).mp hwin
    have hatt : virtualValue (D i).F (D i).f s = maxVirt D hn (Function.update u i s) := by
      simpa only [Function.update_self] using hatt0
    have hpsi : virtualValue (D i).F (D i).f s ≤ virtualValue (D i).F (D i).f s' :=
      hreg hle
    have hM' : maxVirt D hn (Function.update u i s') = virtualValue (D i).F (D i).f s' := by
      apply le_antisymm
      · unfold maxVirt
        apply (Finset.sup'_le_iff _ _).mpr
        intro j _
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self, le_refl]
        · simp only [Function.update_of_ne hji]
          calc
            virtualValue (D j).F (D j).f (u j)
                = virtualValue (D j).F (D j).f ((Function.update u i s) j) := by
              rw [Function.update_of_ne hji]
            _ ≤ maxVirt D hn (Function.update u i s) :=
              virt_le_maxVirt D hn j (Function.update u i s)
            _ = virtualValue (D i).F (D i).f s := hatt.symm
            _ ≤ virtualValue (D i).F (D i).f s' := hpsi
      · simpa only [Function.update_self] using
          virt_le_maxVirt D hn i (Function.update u i s')
    have hMpos' : 0 < maxVirt D hn (Function.update u i s') := by
      rw [hM']
      exact lt_of_lt_of_le (by rwa [hatt]) hpsi
    have hwin' : winner D hn (Function.update u i s') = i := by
      apply (winner_eq_iff D hn (Function.update u i s') i).mpr
      refine ⟨by simpa only [Function.update_self] using hM'.symm, ?_⟩
      intro j hj
      by_cases hji : j = i
      · subst j
        exact le_rfl
      · have hjbound := virt_le_maxVirt D hn j (Function.update u i s)
        have hjold : virtualValue (D j).F (D j).f ((Function.update u i s) j) =
            maxVirt D hn (Function.update u i s) := by
          simp only [Function.update_of_ne hji] at hjbound hj ⊢
          rw [hM'] at hj
          linarith
        exact hleast j hjold
    have h1' : optAlloc D hn i (Function.update u i s') = 1 := by
      unfold optAlloc
      exact Set.indicator_of_mem (show Function.update u i s' ∈
        {t : Fin n → Real | 0 < maxVirt D hn t ∧ winner D hn t = i}
        from ⟨hMpos', hwin'⟩) _
    rw [h1, h1']
  · have hzero : optAlloc D hn i (Function.update u i s) = 0 := by
      unfold optAlloc
      by_cases hmem : 0 < maxVirt D hn (Function.update u i s) ∧
          winner D hn (Function.update u i s) = i
      · have hone : optAlloc D hn i (Function.update u i s) = 1 := by
          unfold optAlloc
          exact Set.indicator_of_mem (show (Function.update u i s) ∈
            {t : Fin n → Real | 0 < maxVirt D hn t ∧ winner D hn t = i}
            from hmem) _
        exact (h1 hone).elim
      · exact Set.indicator_of_notMem (show (Function.update u i s) ∉
          {t : Fin n → Real | 0 < maxVirt D hn t ∧ winner D hn t = i}
          from hmem) _
    rw [hzero]
    exact optAlloc_nonneg D hn i _

lemma optInterim_mono (hreg : Regular D) (i : Fin n) :
    Monotone fun s => optInterim D hn i s := by
  intro s s' hle
  show interimAlloc D (optAlloc D hn) i s ≤ interimAlloc D (optAlloc D hn) i s'
  unfold interimAlloc
  exact integral_mono_ae
    (integrable_update D i (optAlloc D hn) (measurable_optAlloc D hn i)
      (optAlloc_norm_le_one D hn i) s)
    (integrable_update D i (optAlloc D hn) (measurable_optAlloc D hn i)
      (optAlloc_norm_le_one D hn i) s')
    (Filter.Eventually.of_forall fun u => optAlloc_mono_update D hn i u hle (hreg i))

lemma optInterim_eq_zero_of_nonpos (i : Fin n) {s : Real} (hs : s ≤ 0) :
    optInterim D hn i s = 0 := by
  classical
  have hzero : ∀ t : Fin n → Real, optAlloc D hn i (Function.update t i s) = 0 := by
    intro t
    unfold optAlloc
    apply Set.indicator_of_notMem
    rintro ⟨hM, hw⟩
    have hatt : virtualValue (D i).F (D i).f s = maxVirt D hn (Function.update t i s) := by
      simpa only [Function.update_self] using
        ((winner_eq_iff D hn (Function.update t i s) i).mp hw).1
    linarith [virt_nonpos_of_nonpos D hn i hs]
  show (∫ t : Fin n → Real, optAlloc D hn i (Function.update t i s) ∂(jointMu D)) = 0
  simp only [hzero, integral_zero]

lemma integrable_optInterim (i : Fin n) : Integrable (optInterim D hn i) (D i).mu := by
  haveI := (D i).isProb
  apply Integrable.of_bound (measurable_optInterim D hn i).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (optInterim_norm_le_one D hn i)

include hn in
lemma integrable_interimAlloc_of {X : Fin n → (Fin n → Real) → Real}
    (hXmeas : ∀ i, Measurable (X i)) (hXbnd : ∀ i t, ‖X i t‖ ≤ 1) (i : Fin n) :
    Integrable (interimAlloc D X i) (D i).mu := by
  haveI := (D i).isProb
  apply Integrable.of_bound (measurable_interimAlloc D i X (hXmeas i)).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro s
  have hb := norm_integral_le_of_norm_le_const
    (μ := jointMu D) (Filter.Eventually.of_forall fun t => hXbnd i (Function.update t i s))
  simpa only [interimAlloc, Measure.real, measure_univ, ENNReal.toReal_one,
    mul_one] using hb

lemma optUtil_zero (i : Fin n) :
    interimUtility (optInterim D hn i) (optPayment D hn i) 0 = 0 := by
  simp [interimUtility, optPayment]

lemma optPayment_formula (i : Fin n) (t : Real) :
    optPayment D hn i t = t * optInterim D hn i t -
      interimUtility (optInterim D hn i) (optPayment D hn i) 0 -
      ∫ s in (0 : Real)..t, optInterim D hn i s := by
  rw [optUtil_zero D hn i]
  unfold optPayment
  ring

lemma optBIC (hreg : Regular D) (i : Fin n) :
    BIC (optInterim D hn i) (optPayment D hn i) :=
  bic_of_monotone_of_payment _ _ (optInterim_mono D hn hreg i) (optPayment_formula D hn i)

lemma optUtil_eq (hreg : Regular D) (i : Fin n) (t : Real) :
    interimUtility (optInterim D hn i) (optPayment D hn i) t =
      ∫ s in (0 : Real)..t, optInterim D hn i s := by
  have h := envelope_integral _ _ (optBIC D hn hreg i) t
  rwa [optUtil_zero D hn i, sub_zero] at h

lemma optIIR (hreg : Regular D) (i : Fin n) :
    IIR (optInterim D hn i) (optPayment D hn i) := by
  intro t
  rw [optUtil_eq D hn hreg i t]
  rcases le_total 0 t with ht | ht
  · exact intervalIntegral.integral_nonneg_of_ae ht
      (Filter.Eventually.of_forall (optInterim_nonneg D hn i))
  · have hzero : (∫ s in t..0, optInterim D hn i s) = 0 := by
      rw [intervalIntegral.integral_of_le ht]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro s hs
      exact optInterim_eq_zero_of_nonpos D hn i (Set.mem_Ioc.mp hs).2
    rw [intervalIntegral.integral_symm t 0, hzero, neg_zero]

/-- The envelope primitive is measurable, even without local integrability. -/
lemma measurable_primitive {x : Real → Real} (hx : Measurable x) :
    Measurable fun t : Real => ∫ s in (0 : Real)..t, x s := by
  classical
  have hpos : Measurable (fun p : Real × Real => (Set.Ioc 0 p.2).indicator x p.1) := by
    have heq : (fun p : Real × Real => (Set.Ioc 0 p.2).indicator x p.1) =
        {p : Real × Real | p.1 ∈ Set.Ioc 0 p.2}.indicator (fun p => x p.1) := by
      funext p
      rfl
    rw [heq]
    apply (hx.comp measurable_fst).indicator
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_snd)
  have hneg : Measurable (fun p : Real × Real => (Set.Ioc p.2 0).indicator x p.1) := by
    have heq : (fun p : Real × Real => (Set.Ioc p.2 0).indicator x p.1) =
        {p : Real × Real | p.1 ∈ Set.Ioc p.2 0}.indicator (fun p => x p.1) := by
      funext p
      rfl
    rw [heq]
    apply (hx.comp measurable_fst).indicator
    exact (measurableSet_lt measurable_snd measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  have hm : Measurable (fun t : Real =>
      (∫ s : Real, (Set.Ioc 0 t).indicator x s) -
      ∫ s : Real, (Set.Ioc t 0).indicator x s) :=
    (hpos.stronglyMeasurable.integral_prod_left' (μ := volume)).measurable.sub
      (hneg.stronglyMeasurable.integral_prod_left' (μ := volume)).measurable
  have heq : (fun t : Real =>
      (∫ s : Real, (Set.Ioc 0 t).indicator x s) -
      ∫ s : Real, (Set.Ioc t 0).indicator x s) =
      (fun t : Real => ∫ s in (0 : Real)..t, x s) := by
    funext t
    rw [integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
    rfl
  rwa [heq] at hm

/-- A measurable allocation bounded between zero and one has an integrable primitive
against any measure with an integrable first moment. -/
lemma integrable_primitive {x : Real → Real} (hx_meas : Measurable x)
    (hx_nn : ∀ s, 0 ≤ x s) (hx_le : ∀ s, x s ≤ 1) (mu : Measure Real)
    (hInt_id : Integrable (fun t : Real => t) mu) :
    Integrable (fun t => ∫ s in (0 : Real)..t, x s) mu := by
  refine Integrable.mono' hInt_id.norm (measurable_primitive hx_meas).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have hbound : ∀ s : Real, ‖x s‖ ≤ 1 := by
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (hx_nn s)]
    exact hx_le s
  simpa only [one_mul, sub_zero, Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := 1)
      (fun s _ => hbound s))

lemma integrable_optPayment (i : Fin n)
    (hInt_id : Integrable (fun t : Real => t) (D i).mu) :
    Integrable (optPayment D hn i) (D i).mu := by
  unfold optPayment
  apply Integrable.sub
  · exact hInt_id.mul_bdd (measurable_optInterim D hn i).aestronglyMeasurable
      (Filter.Eventually.of_forall (optInterim_norm_le_one D hn i))
  · exact integrable_primitive (measurable_optInterim D hn i)
      (optInterim_nonneg D hn i) (optInterim_le_one D hn i) _ hInt_id

include hn in
lemma integrable_abs_psi (i : Fin n)
    (hpsi : Integrable (fun t => virtualValue (D i).F (D i).f t) (D i).mu) :
    Integrable (fun t : Fin n → Real => ‖virtualValue (D i).F (D i).f (t i)‖)
      (jointMu D) := by
  have hprod := (integrable_psi_fst D i _ hpsi).norm
  have hcomp := ((measurePreserving_splitEquiv D i).integrable_comp
    hprod.aestronglyMeasurable).mpr hprod
  have heq : (fun a : Real × ({j : Fin n // j ≠ i} → Real) =>
        ‖virtualValue (D i).F (D i).f a.1‖) ∘ (splitEquiv D i)
      = (fun t : Fin n → Real => ‖virtualValue (D i).F (D i).f (t i)‖) := by
    funext t
    simp only [Function.comp_apply, splitEquiv_apply]
  rw [heq] at hcomp
  exact hcomp

lemma integrable_maxVirt_nonneg
    (hInt_psi : ∀ i, Integrable (fun t => virtualValue (D i).F (D i).f t) (D i).mu) :
    Integrable (fun t : Fin n → Real => max 0 (maxVirt D hn t)) (jointMu D) := by
  classical
  refine Integrable.mono'
    (integrable_finsetSum Finset.univ (fun i _ => integrable_abs_psi D hn i (hInt_psi i)))
    (measurable_const.max (measurable_maxVirt D hn)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left 0 _)]
  apply max_le (Finset.sum_nonneg fun i _ => norm_nonneg _)
  have hatt := (Finset.mem_filter.mp (winner_mem D hn t)).2
  calc
    maxVirt D hn t = virtualValue (D (winner D hn t)).F
        (D (winner D hn t)).f (t (winner D hn t)) := hatt.symm
    _ ≤ ‖virtualValue (D (winner D hn t)).F
        (D (winner D hn t)).f (t (winner D hn t))‖ := Real.le_norm_self _
    _ ≤ ∑ i, ‖virtualValue (D i).F (D i).f (t i)‖ := by
      have hsplit := Finset.add_sum_erase Finset.univ
        (fun i => ‖virtualValue (D i).F (D i).f (t i)‖)
        (Finset.mem_univ (winner D hn t))
      have hnn : 0 ≤ ∑ i ∈ Finset.univ.erase (winner D hn t),
          ‖virtualValue (D i).F (D i).f (t i)‖ :=
        Finset.sum_nonneg fun i _ => norm_nonneg _
      linarith

/-- For regular priors, the maximum-positive-virtual-value auction with envelope
payments is BIC, interim individually rational, and revenue optimal. -/
theorem optimalAuction (hreg : Regular D)
    (hsupp : ∀ i (t : Real), 0 < t → 0 < (D i).F t)
    (hInt_id : ∀ i, Integrable (fun t : Real => t) (D i).mu)
    (hInt_psi : ∀ i, Integrable (fun t : Real => virtualValue (D i).F (D i).f t) (D i).mu)
    (hInt_xw_star : ∀ i, Integrable (fun s => optInterim D hn i s * (1 - (D i).F s)) volume)
    (X : Fin n → (Fin n → Real) → Real)
    (hXmeas : ∀ i, Measurable (X i)) (hXnn : ∀ i t, 0 ≤ X i t)
    (hXsum : ∀ t, ∑ i, X i t ≤ 1)
    (p : Fin n → Real → Real)
    (hBIC : ∀ i, BIC (interimAlloc D X i) (p i))
    (hIIR : ∀ i, IIR (interimAlloc D X i) (p i))
    (hInt_p : ∀ i, Integrable (p i) (D i).mu)
    (hInt_xw : ∀ i, Integrable (fun s => interimAlloc D X i s * (1 - (D i).F s)) volume) :
    (∀ i, BIC (optInterim D hn i) (optPayment D hn i)) ∧
      (∀ i, IIR (optInterim D hn i) (optPayment D hn i)) ∧
      ∑ i, expectedPayment (p i) (D i) ≤
        ∑ i, expectedPayment (optPayment D hn i) (D i) := by
  classical
  haveI := fun i => (D i).isProb
  refine ⟨fun i => optBIC D hn hreg i, fun i => optIIR D hn hreg i, ?_⟩
  have hXbnd : ∀ i t, ‖X i t‖ ≤ 1 := by
    intro i t
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨by linarith [hXnn i t], ?_⟩
    have hsplit := Finset.add_sum_erase Finset.univ (fun j => X j t) (Finset.mem_univ i)
    have hnn : 0 ≤ ∑ j ∈ Finset.univ.erase i, X j t :=
      Finset.sum_nonneg fun j _ => hXnn j t
    linarith [hXsum t]
  have key : ∀ i, expectedPayment (p i) (D i) ≤
      ∫ t, virtualValue (D i).F (D i).f (t i) * X i t ∂(jointMu D) := by
    intro i
    have hxmeas := measurable_interimAlloc D i X (hXmeas i)
    have hxnn : ∀ s, 0 ≤ interimAlloc D X i s := interimAlloc_nonneg D i X hXnn
    have hxle : ∀ s, interimAlloc D X i s ≤ 1 := interimAlloc_le_one D i X hXmeas hXbnd
    have hx1 : ∀ s, ‖interimAlloc D X i s‖ ≤ 1 := by
      intro s
      rw [Real.norm_eq_abs, abs_of_nonneg (hxnn s)]
      exact hxle s
    have hInt_tx : Integrable (fun t => t * interimAlloc D X i t) (D i).mu :=
      (hInt_id i).mul_bdd hxmeas.aestronglyMeasurable (Filter.Eventually.of_forall hx1)
    have hIntG := integrable_primitive hxmeas hxnn hxle (D i).mu (hInt_id i)
    have hInt_psix : Integrable
        (fun t => virtualValue (D i).F (D i).f t * interimAlloc D X i t) (D i).mu :=
      (hInt_psi i).mul_bdd hxmeas.aestronglyMeasurable (Filter.Eventually.of_forall hx1)
    have hM3 := virtualSurplusIdentity (interimAlloc D X i) (p i) (D i)
      (hBIC i) (hsupp i) (hInt_p i) hInt_tx hIntG (hInt_xw i) hInt_psix
    have hV : expectedVirtualSurplus (interimAlloc D X i) (D i) =
        ∫ t, virtualValue (D i).F (D i).f (t i) * X i t ∂(jointMu D) :=
      fubini_coord D i (fun t => virtualValue (D i).F (D i).f t) X
        (hXmeas i) (hXbnd i) (hInt_psi i)
    rw [hM3, hV]
    have hU0 := hIIR i 0
    linarith
  have hopt : ∀ i, expectedPayment (optPayment D hn i) (D i) =
      ∫ t, virtualValue (D i).F (D i).f (t i) * optAlloc D hn i t ∂(jointMu D) := by
    intro i
    have hInt_tx : Integrable (fun t => t * optInterim D hn i t) (D i).mu :=
      (hInt_id i).mul_bdd (measurable_optInterim D hn i).aestronglyMeasurable
        (Filter.Eventually.of_forall (optInterim_norm_le_one D hn i))
    have hIntG := integrable_primitive (measurable_optInterim D hn i)
      (optInterim_nonneg D hn i) (optInterim_le_one D hn i) (D i).mu (hInt_id i)
    have hInt_psix : Integrable
        (fun t => virtualValue (D i).F (D i).f t * optInterim D hn i t) (D i).mu :=
      (hInt_psi i).mul_bdd (measurable_optInterim D hn i).aestronglyMeasurable
        (Filter.Eventually.of_forall (optInterim_norm_le_one D hn i))
    have hM3 := virtualSurplusIdentity (optInterim D hn i) (optPayment D hn i) (D i)
      (optBIC D hn hreg i) (hsupp i) (integrable_optPayment D hn i (hInt_id i))
      hInt_tx hIntG (hInt_xw_star i) hInt_psix
    rw [optUtil_zero D hn i, sub_zero] at hM3
    have hV : expectedVirtualSurplus (optInterim D hn i) (D i) =
        ∫ t, virtualValue (D i).F (D i).f (t i) * optAlloc D hn i t ∂(jointMu D) :=
      fubini_coord D i (fun t => virtualValue (D i).F (D i).f t) (optAlloc D hn)
        (measurable_optAlloc D hn i) (optAlloc_norm_le_one D hn i) (hInt_psi i)
    exact hM3.trans hV
  have hsum1 :
      (∑ i, ∫ t, virtualValue (D i).F (D i).f (t i) * X i t ∂(jointMu D)) =
      ∫ t, ∑ i, virtualValue (D i).F (D i).f (t i) * X i t ∂(jointMu D) :=
    (integral_finsetSum Finset.univ (fun i _ =>
      integrable_psiX D i _ X (hXmeas i) (hXbnd i) (hInt_psi i))).symm
  have hle :
      (∫ t, ∑ i, virtualValue (D i).F (D i).f (t i) * X i t ∂(jointMu D)) ≤
      ∫ t, max 0 (maxVirt D hn t) ∂(jointMu D) :=
    integral_mono_ae
      (integrable_finsetSum Finset.univ (fun i _ =>
        integrable_psiX D i _ X (hXmeas i) (hXbnd i) (hInt_psi i)))
      (integrable_maxVirt_nonneg D hn hInt_psi)
      (Filter.Eventually.of_forall fun t => virtSurplus_le D hn X hXnn hXsum t)
  have hsum2 :
      (∑ i, ∫ t, virtualValue (D i).F (D i).f (t i) * optAlloc D hn i t ∂(jointMu D)) =
      ∫ t, max 0 (maxVirt D hn t) ∂(jointMu D) := by
    rw [(integral_finsetSum Finset.univ (fun i _ =>
      integrable_psiX D i _ (optAlloc D hn) (measurable_optAlloc D hn i)
        (optAlloc_norm_le_one D hn i) (hInt_psi i))).symm]
    exact integral_congr_ae (Filter.Eventually.of_forall (virtSurplus_opt D hn))
  calc
    ∑ i, expectedPayment (p i) (D i)
        ≤ ∑ i, ∫ t, virtualValue (D i).F (D i).f (t i) * X i t ∂(jointMu D) :=
      Finset.sum_le_sum fun i _ => key i
    _ = ∫ t, ∑ i, virtualValue (D i).F (D i).f (t i) * X i t ∂(jointMu D) := hsum1
    _ ≤ ∫ t, max 0 (maxVirt D hn t) ∂(jointMu D) := hle
    _ = ∑ i, expectedPayment (optPayment D hn i) (D i) := by
      rw [← hsum2]
      exact Finset.sum_congr rfl fun i _ => (hopt i).symm

end Myerson
