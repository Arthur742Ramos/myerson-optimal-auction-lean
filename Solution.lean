import Myerson.Main

open MeasureTheory

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
    expectedPayment p D = expectedVirtualSurplus x D - interimUtility x p 0 :=
  _root_.MyersonOptimalAuction.virtualSurplusIdentity x p D hBIC hsupp _hInt_p hInt_tx hIntG
    hInt_xw _hInt_psix

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
        ∑ i, expectedPayment (_root_.Myerson.optPayment D hn i) (D i) :=
  _root_.Myerson.optimalAuction D hn hreg hsupp hInt_id hInt_psi hInt_xw_star X hXmeas hXnn
    hXsum p hBIC hIIR hInt_p hInt_xw

end Palomar

end MyersonOptimalAuction
