module

public import Myerson.VirtualSurplus
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Prod
public import Myerson.Dist

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Myerson

variable {n : Nat} (D : Fin n → TypeDist)

/-- Joint prior over type profiles: the product of the marginal type measures. -/
public noncomputable abbrev jointMu : Measure (Fin n → Real) :=
  Measure.pi fun j => (D j).mu

/-- Interim allocation rule induced by an ex post allocation rule X. -/
@[expose] public noncomputable def interimAlloc (X : Fin n → (Fin n → Real) → Real)
    (i : Fin n) (s : Real) : Real :=
  ∫ t, X i (Function.update t i s) ∂(jointMu D)

public instance : IsProbabilityMeasure (jointMu D) := by
  haveI := fun j => (D j).isProb
  exact Measure.pi.instIsProbabilityMeasure (fun j => (D j).mu)

/-- Splitting a type profile into bidder i's type and everyone else's types. -/
@[expose] public noncomputable def splitEquiv (D : Fin n → TypeDist) (i : Fin n) :
    (Fin n → Real) ≃ᵐ Real × ({j : Fin n // j ≠ i} → Real) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Real) (fun j => j = i)).trans
    ((MeasurableEquiv.piUnique _).prodCongr (MeasurableEquiv.refl _))

@[simp] public lemma splitEquiv_apply (i : Fin n) (t : Fin n → Real) :
    splitEquiv D i t = (t i, fun j : {j : Fin n // j ≠ i} => t j.val) := by
  change (t i, fun j : {j : Fin n // j ≠ i} => t j.val) = _
  rfl

@[simp] public lemma splitEquiv_symm_apply (i : Fin n)
    (p : Real × ({j : Fin n // j ≠ i} → Real)) (j : Fin n) :
    (splitEquiv D i).symm p j = if h : j = i then p.1 else p.2 ⟨j, h⟩ := by
  change (if h : j = i then p.1 else p.2 ⟨j, h⟩) = _
  rfl

public lemma splitEquiv_symm_i (i : Fin n)
    (p : Real × ({j : Fin n // j ≠ i} → Real)) :
    (splitEquiv D i).symm p i = p.1 := by
  rw [splitEquiv_symm_apply]
  exact dite_eq_left rfl

/-- Updating the i-coordinate of a split profile only changes the i-coordinate. -/
public lemma update_symm_eq (i : Fin n) (s s' : Real)
    (u : {j : Fin n // j ≠ i} → Real) :
    Function.update ((splitEquiv D i).symm (s', u)) i s
      = (splitEquiv D i).symm (s, u) := by
  funext j
  by_cases h : j = i
  · subst j
    simp only [Function.update_self, splitEquiv_symm_i]
  · simp only [Function.update_of_ne h, splitEquiv_symm_apply, dite_eq_right h]

/-- The splitting equivalence preserves the product measure. -/
public lemma measurePreserving_splitEquiv (i : Fin n) :
    MeasurePreserving (splitEquiv D i) (jointMu D)
      ((D i).mu.prod (Measure.pi fun j : {j : Fin n // j ≠ i} => (D j.val).mu)) := by
  haveI := fun j => (D j).isProb
  haveI := fun j : {j : Fin n // j = i} => (D j.val).isProb
  haveI := fun j : {j : Fin n // j ≠ i} => (D j.val).isProb
  -- `measurePreserving_piEquivPiSubtypeProd` uses the `Subtype.fintype` instance on
  -- `{j // j = i}`; convert it to the `Fintype.subtypeEq i` instance found by TC here.
  -- (`Fintype` is a subsingleton, so the instances are propositionally equal.)
  have hFintype : (Subtype.fintype (fun j : Fin n => j = i)) = (Fintype.subtypeEq i) :=
    Subsingleton.elim _ _
  have hsplit :
      MeasurePreserving
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Real) (fun j => j = i))
        (jointMu D)
        ((Measure.pi fun j : {j : Fin n // j = i} => (D j.val).mu).prod
          (Measure.pi fun j : {j : Fin n // j ≠ i} => (D j.val).mu)) := by
    have h := measurePreserving_piEquivPiSubtypeProd (α := fun _ : Fin n => Real)
      (fun j => (D j).mu) (fun j => j = i)
    rwa [hFintype] at h
  have hfirst :
      MeasurePreserving (MeasurableEquiv.piUnique (fun _ : {j : Fin n // j = i} => Real))
        (Measure.pi fun j : {j : Fin n // j = i} => (D j.val).mu) (D i).mu := by
    exact measurePreserving_piUnique (fun j : {j : Fin n // j = i} => (D j.val).mu)
  have hcollapse :
      MeasurePreserving
        ((MeasurableEquiv.piUnique (fun _ : {j : Fin n // j = i} => Real)).prodCongr
          (MeasurableEquiv.refl ({j : Fin n // j ≠ i} → Real)))
        ((Measure.pi fun j : {j : Fin n // j = i} => (D j.val).mu).prod
          (Measure.pi fun j : {j : Fin n // j ≠ i} => (D j.val).mu))
        ((D i).mu.prod (Measure.pi fun j : {j : Fin n // j ≠ i} => (D j.val).mu)) := by
    exact MeasurePreserving.prod hfirst
      (MeasurePreserving.id (Measure.pi fun j : {j : Fin n // j ≠ i} => (D j.val).mu))
  exact MeasurePreserving.trans hsplit hcollapse

public lemma measurable_update (D : Fin n → TypeDist) (i : Fin n) (s : Real) :
    Measurable fun t : Fin n → Real => Function.update t i s := by
  apply measurable_pi_iff.mpr
  intro j
  by_cases h : j = i
  · subst j
    simpa only [Function.update_self] using
      (measurable_const : Measurable fun _ : Fin n → Real => s)
  · simpa only [Function.update_of_ne h] using (measurable_pi_apply j)

public lemma integrable_update (i : Fin n) (X : Fin n → (Fin n → Real) → Real)
    (hXmeas : Measurable (X i)) (hXbnd : ∀ t, ‖X i t‖ ≤ 1) (s : Real) :
    Integrable (fun t => X i (Function.update t i s)) (jointMu D) := by
  apply Integrable.of_bound
    (hXmeas.comp (measurable_update D i s)).aestronglyMeasurable 1
  exact ae_of_all _ fun t => hXbnd (Function.update t i s)

public lemma interimAlloc_nonneg (i : Fin n) (X : Fin n → (Fin n → Real) → Real)
    (hXnn : ∀ i t, 0 ≤ X i t) (s : Real) :
    0 ≤ interimAlloc D X i s := by
  unfold interimAlloc
  exact integral_nonneg fun t => hXnn i (Function.update t i s)

public lemma interimAlloc_le_one (i : Fin n) (X : Fin n → (Fin n → Real) → Real)
    (hXmeas : ∀ i, Measurable (X i)) (hXbnd : ∀ i t, ‖X i t‖ ≤ 1) (s : Real) :
    interimAlloc D X i s ≤ 1 := by
  unfold interimAlloc
  calc
    (∫ t, X i (Function.update t i s) ∂(jointMu D))
        ≤ ∫ _ : Fin n → Real, (1 : Real) ∂(jointMu D) := by
          apply integral_mono_ae (integrable_update D i X (hXmeas i) (hXbnd i) s)
            (integrable_const 1)
          filter_upwards with t
          exact (Real.le_norm_self _).trans (hXbnd i (Function.update t i s))
    _ = 1 := by
      rw [integral_const]
      change ((jointMu D) Set.univ).toReal • (1 : Real) = 1
      rw [measure_univ, ENNReal.toReal_one, one_smul]

public lemma measurable_interimAlloc (i : Fin n) (X : Fin n → (Fin n → Real) → Real)
    (hXmeas : Measurable (X i)) :
    Measurable (interimAlloc D X i) := by
  have hupdate :
      Measurable fun p : (Fin n → Real) × Real => Function.update p.1 i p.2 := by
    apply measurable_pi_iff.mpr
    intro j
    by_cases h : j = i
    · subst j
      simpa only [Function.update_self] using
        (measurable_snd : Measurable fun p : (Fin n → Real) × Real => p.2)
    · have hmj : Measurable (fun p : (Fin n → Real) × Real => p.1 j) :=
        (measurable_pi_apply j).comp
          (measurable_fst : Measurable fun p : (Fin n → Real) × Real => p.1)
      simpa only [Function.update_of_ne h] using hmj
  have hmeas :
      Measurable fun p : (Fin n → Real) × Real => X i (Function.update p.1 i p.2) :=
    hXmeas.comp hupdate
  exact (hmeas.stronglyMeasurable.integral_prod_left' (μ := jointMu D)).measurable

public lemma integrable_psi_fst (i : Fin n) (ψ : Real → Real) (hψ : Integrable ψ (D i).mu) :
    Integrable (fun p : Real × ({j : Fin n // j ≠ i} → Real) => ψ p.1)
      ((D i).mu.prod (Measure.pi fun j : {j : Fin n // j ≠ i} => (D j.val).mu)) := by
  haveI := fun j : {j : Fin n // j ≠ i} => (D j.val).isProb
  have hmeas :
      AEStronglyMeasurable (fun p : Real × ({j : Fin n // j ≠ i} → Real) => ψ p.1)
        ((D i).mu.prod (Measure.pi fun j : {j : Fin n // j ≠ i} => (D j.val).mu)) :=
    hψ.aestronglyMeasurable.comp_fst
  refine ⟨hmeas, ?_⟩
  have hfin : ∫⁻ s, ‖ψ s‖ₑ ∂(D i).mu < ∞ :=
    hasFiniteIntegral_iff_enorm.mp hψ.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm]
  have heq : (∫⁻ p, ‖ψ p.1‖ₑ ∂((D i).mu.prod
      (Measure.pi fun j : {j : Fin n // j ≠ i} => (D j.val).mu)))
      = ∫⁻ s, ‖ψ s‖ₑ ∂(D i).mu := by
    rw [lintegral_prod _ (hmeas.aemeasurable).enorm]
    apply lintegral_congr_ae
    filter_upwards with s
    show (∫⁻ y : ({j : Fin n // j ≠ i} → Real),
      ‖ψ (s, y).1‖ₑ ∂(Measure.pi fun j => (D j.val).mu)) = _
    rw [show (fun y : ({j : Fin n // j ≠ i} → Real) => ‖ψ (s, y).1‖ₑ)
        = (fun _ => ‖ψ s‖ₑ) from rfl,
      lintegral_const, measure_univ, mul_one]
  rw [heq]
  exact hfin

/-- Integrability of ψ(s) * X i (reassembled profile) on the split product. -/
public lemma integrable_psiX_prod (i : Fin n) (ψ : Real → Real)
    (X : Fin n → (Fin n → Real) → Real)
    (hXmeas : Measurable (X i)) (hXbnd : ∀ t, ‖X i t‖ ≤ 1)
    (hψ : Integrable ψ (D i).mu) :
    Integrable (fun p : Real × ({j : Fin n // j ≠ i} → Real) =>
      ψ p.1 * X i ((splitEquiv D i).symm p))
      ((D i).mu.prod (Measure.pi fun j : {j : Fin n // j ≠ i} => (D j.val).mu)) := by
  have hprod := (integrable_psi_fst D i ψ hψ).bdd_mul
    (hXmeas.comp (splitEquiv D i).symm.measurable).aestronglyMeasurable
    (ae_of_all _ fun p => hXbnd ((splitEquiv D i).symm p))
  apply hprod.congr
  filter_upwards with p
  exact mul_comm _ _

/-- Transported to the joint prior. -/
public lemma integrable_psiX (i : Fin n) (ψ : Real → Real)
    (X : Fin n → (Fin n → Real) → Real)
    (hXmeas : Measurable (X i)) (hXbnd : ∀ t, ‖X i t‖ ≤ 1)
    (hψ : Integrable ψ (D i).mu) :
    Integrable (fun t => ψ (t i) * X i t) (jointMu D) := by
  have hprod := integrable_psiX_prod D i ψ X hXmeas hXbnd hψ
  have hcomp := ((measurePreserving_splitEquiv D i).integrable_comp
    hprod.aestronglyMeasurable).mpr hprod
  have heq :
      (fun p : Real × ({j : Fin n // j ≠ i} → Real) =>
        ψ p.1 * X i ((splitEquiv D i).symm p)) ∘ (splitEquiv D i)
        = (fun t : Fin n → Real => ψ (t i) * X i t) := by
    funext t
    show ψ (t i) * X i ((splitEquiv D i).symm (splitEquiv D i t)) = _
    rw [MeasurableEquiv.symm_apply_apply]
  rw [heq] at hcomp
  exact hcomp

/-- Fubini across bidder i's coordinate: the interim expectation of ψ against the
interim allocation equals the ex post expectation of ψ(t i) against X. -/
public theorem fubini_coord (i : Fin n) (ψ : Real → Real)
    (X : Fin n → (Fin n → Real) → Real)
    (hXmeas : Measurable (X i))
    (hXbnd : ∀ t, ‖X i t‖ ≤ 1)
    (hψ : Integrable ψ (D i).mu) :
    ∫ s, ψ s * interimAlloc D X i s ∂(D i).mu
      = ∫ t, ψ (t i) * X i t ∂(jointMu D) := by
  haveI := fun j : {j : Fin n // j ≠ i} => (D j.val).isProb
  haveI := (D i).isProb
  let μm : Measure ({j : Fin n // j ≠ i} → Real) :=
    Measure.pi fun j : {j : Fin n // j ≠ i} => (D j.val).mu
  have hsymm : MeasurePreserving (splitEquiv D i).symm ((D i).mu.prod μm) (jointMu D) :=
    MeasurePreserving.symm (splitEquiv D i) (measurePreserving_splitEquiv D i)
  -- Step 1: the interim allocation is the integral over the other bidders' types.
  have hinterim : ∀ s : Real, interimAlloc D X i s
      = ∫ u, X i ((splitEquiv D i).symm (s, u)) ∂μm := by
    intro s
    have hupdate := integrable_update D i X hXmeas hXbnd s
    have hcomp :
        Integrable (fun p : Real × ({j : Fin n // j ≠ i} → Real) =>
          X i (Function.update ((splitEquiv D i).symm p) i s)) ((D i).mu.prod μm) :=
      (hsymm.integrable_comp hupdate.aestronglyMeasurable).mpr hupdate
    have heq :
        (fun p : Real × ({j : Fin n // j ≠ i} → Real) =>
          X i (Function.update ((splitEquiv D i).symm p) i s))
          = (fun p => X i ((splitEquiv D i).symm (s, p.2))) := by
      funext p
      obtain ⟨s', u⟩ := p
      rw [update_symm_eq]
    have hprod :
        Integrable (fun p : Real × ({j : Fin n // j ≠ i} → Real) =>
          X i ((splitEquiv D i).symm (s, p.2))) ((D i).mu.prod μm) := by
      rw [← heq]
      exact hcomp
    calc
      interimAlloc D X i s
          = ∫ p, X i (Function.update ((splitEquiv D i).symm p) i s)
              ∂((D i).mu.prod μm) :=
            (hsymm.integral_comp' (fun t => X i (Function.update t i s))).symm
      _ = ∫ p, X i ((splitEquiv D i).symm (s, p.2)) ∂((D i).mu.prod μm) := by
        rw [heq]
      _ = ∫ _ : Real, (∫ u, X i ((splitEquiv D i).symm (s, u)) ∂μm) ∂(D i).mu :=
        integral_prod _ hprod
      _ = ∫ u, X i ((splitEquiv D i).symm (s, u)) ∂μm := by
        rw [integral_const]
        change ((D i).mu Set.univ).toReal •
          (∫ u, X i ((splitEquiv D i).symm (s, u)) ∂μm) = _
        rw [measure_univ, ENNReal.toReal_one, one_smul]
  -- Step 2: put the weight inside the fiber integral and apply Fubini.
  have hprod := integrable_psiX_prod D i ψ X hXmeas hXbnd hψ
  -- Step 3: the product integrand is the ex post integrand composed with the inverse split.
  have htransport :
      (fun p : Real × ({j : Fin n // j ≠ i} → Real) =>
        ψ p.1 * X i ((splitEquiv D i).symm p))
        = (fun t : Fin n → Real => ψ (t i) * X i t) ∘ (splitEquiv D i).symm := by
    funext p
    simp only [Function.comp_apply, splitEquiv_symm_i]
  calc
    (∫ s, ψ s * interimAlloc D X i s ∂(D i).mu)
        = ∫ s, ∫ u, ψ s * X i ((splitEquiv D i).symm (s, u)) ∂μm ∂(D i).mu := by
          apply integral_congr_ae
          filter_upwards with s
          rw [hinterim s, integral_const_mul]
    _ = ∫ p, ψ p.1 * X i ((splitEquiv D i).symm p) ∂((D i).mu.prod μm) :=
      (integral_prod _ hprod).symm
    _ = ∫ t, ψ (t i) * X i t ∂(jointMu D) := by
      rw [htransport]
      exact hsymm.integral_comp' (fun t => ψ (t i) * X i t)

end Myerson
