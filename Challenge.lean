import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Finset.Max

open MeasureTheory
open scoped ENNReal

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

noncomputable section

namespace MyersonOptimalAuction

/-- Virtual value is the type minus the inverse hazard rate. -/
def virtualValue (F f : Real → Real) (t : Real) : Real := t - (1 - F t) / f t

/-- Regularity requires each bidder to have a monotone virtual value function. -/
def Regular {n : Nat} (D : Fin n → TypeDist) : Prop :=
  ∀ i, Monotone fun t => virtualValue (D i).F (D i).f t

/-- Interim utility of a bidder with type t facing interim allocation rule x
and interim payment rule p (quasi-linear utility). -/
def interimUtility (x p : Real → Real) (t : Real) : Real := t * x t - p t

/-- Bayesian incentive compatibility, truthful reporting maximizes interim
utility over all possible reports. -/
def BIC (x p : Real → Real) : Prop :=
  ∀ t r, t * x r - p r ≤ interimUtility x p t

/-- Interim individual rationality, participation is weakly better than the
outside option of zero. -/
def IIR (x p : Real → Real) : Prop := ∀ t, 0 ≤ interimUtility x p t

/-- Ex ante expected payment under the type distribution D. -/
noncomputable def expectedPayment (p : Real → Real) (D : TypeDist) : Real :=
  ∫ t, p t ∂D.mu

/-- Ex ante expected virtual surplus under the type distribution D. -/
noncomputable def expectedVirtualSurplus (x : Real → Real) (D : TypeDist) : Real :=
  ∫ t, virtualValue D.F D.f t * x t ∂D.mu

end MyersonOptimalAuction

namespace Myerson

open MyersonOptimalAuction

variable {n : Nat} (D : Fin n → TypeDist) (hn : 0 < n)

/-- Joint prior over type profiles: the product of the marginal type measures. -/
noncomputable abbrev jointMu : Measure (Fin n → Real) :=
  Measure.pi fun j => (D j).mu

/-- Interim allocation rule induced by an ex post allocation rule X. -/
noncomputable def interimAlloc (X : Fin n → (Fin n → Real) → Real)
    (i : Fin n) (s : Real) : Real :=
  ∫ t, X i (Function.update t i s) ∂(jointMu D)

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

/-- Allocate to the selected bidder exactly when the largest virtual value is positive. -/
noncomputable def optAlloc (i : Fin n) : (Fin n → Real) → Real :=
  {t : Fin n → Real | 0 < maxVirt D hn t ∧ winner D hn t = i}.indicator 1

/-- Interim allocation of the optimal auction for bidder i. -/
noncomputable def optInterim (i : Fin n) : Real → Real :=
  interimAlloc D (optAlloc D hn) i

/-- Envelope payments of the optimal auction, normalized to utility zero at type zero. -/
noncomputable def optPayment (i : Fin n) (t : Real) : Real :=
  t * optInterim D hn i t - ∫ s in (0 : Real)..t, optInterim D hn i s

end Myerson

namespace MyersonOptimalAuction

namespace Palomar

/-- Virtual-surplus revenue identity: under BIC, the expected payment equals the
expected virtual surplus minus the reference-type (type zero) interim utility. -/
theorem virtualSurplusIdentity (x p : Real → Real) (D : TypeDist)
    (hBIC : BIC x p)
    (hsupp : ∀ t : Real, 0 < t → 0 < D.F t)
    (_hInt_p : Integrable p D.mu)
    (hInt_tx : Integrable (fun t => t * x t) D.mu)
    (hIntG : Integrable (fun t => ∫ s in (0:Real)..t, x s) D.mu)
    (hInt_xw : Integrable (fun s => x s * (1 - D.F s)) volume)
    (_hInt_psix : Integrable (fun t => virtualValue D.F D.f t * x t) D.mu) :
    expectedPayment p D = expectedVirtualSurplus x D - interimUtility x p 0 := by
  sorry

/-- Myerson's optimal auction theorem (regular case): with independent regular
priors, the auction that allocates to the highest nonnegative virtual value
(with deterministic tie-breaking) and charges envelope payments is Bayesian
incentive compatible and interim individually rational, and it raises at least
as much expected revenue as any feasible BIC and interim-IR mechanism. -/
theorem optimalAuction {n : Nat} (D : Fin n → TypeDist) (hn : 0 < n)
    (hreg : Regular D)
    (hsupp : ∀ i (t : Real), 0 < t → 0 < (D i).F t)
    (hInt_id : ∀ i, Integrable (fun t : Real => t) (D i).mu)
    (hInt_psi : ∀ i, Integrable (fun t : Real => virtualValue (D i).F (D i).f t) (D i).mu)
    (hInt_xw_star : ∀ i,
      Integrable (fun s => _root_.Myerson.optInterim D hn i s * (1 - (D i).F s)) volume)
    (X : Fin n → (Fin n → Real) → Real)
    (hXmeas : ∀ i, Measurable (X i)) (hXnn : ∀ i t, 0 ≤ X i t)
    (hXsum : ∀ t, ∑ i, X i t ≤ 1)
    (p : Fin n → Real → Real)
    (hBIC : ∀ i, BIC (_root_.Myerson.interimAlloc D X i) (p i))
    (hIIR : ∀ i, IIR (_root_.Myerson.interimAlloc D X i) (p i))
    (hInt_p : ∀ i, Integrable (p i) (D i).mu)
    (hInt_xw : ∀ i,
      Integrable (fun s => _root_.Myerson.interimAlloc D X i s * (1 - (D i).F s)) volume) :
    (∀ i, BIC (_root_.Myerson.optInterim D hn i) (_root_.Myerson.optPayment D hn i)) ∧
      (∀ i, IIR (_root_.Myerson.optInterim D hn i) (_root_.Myerson.optPayment D hn i)) ∧
      ∑ i, expectedPayment (p i) (D i) ≤
        ∑ i, expectedPayment (_root_.Myerson.optPayment D hn i) (D i) := by
  sorry

end Palomar

end MyersonOptimalAuction
