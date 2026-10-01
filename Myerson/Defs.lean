module

public import Myerson.Dist

open MeasureTheory

noncomputable section

namespace MyersonOptimalAuction

/-- Virtual value is the type minus the inverse hazard rate. -/
@[expose] public def virtualValue (F f : Real → Real) (t : Real) : Real := t - (1 - F t) / f t

/-- Regularity requires each bidder to have a monotone virtual value function. -/
@[expose] public def Regular {n : Nat} (D : Fin n → TypeDist) : Prop :=
  ∀ i, Monotone fun t => virtualValue (D i).F (D i).f t

/-- Interim utility of a bidder with type t facing interim allocation rule x
and interim payment rule p (quasi-linear utility). -/
@[expose] public def interimUtility (x p : Real → Real) (t : Real) : Real := t * x t - p t

/-- Bayesian incentive compatibility, truthful reporting maximizes interim
utility over all possible reports. -/
@[expose] public def BIC (x p : Real → Real) : Prop :=
  ∀ t r, t * x r - p r ≤ interimUtility x p t

/-- Interim individual rationality, participation is weakly better than the
outside option of zero. -/
@[expose] public def IIR (x p : Real → Real) : Prop := ∀ t, 0 ≤ interimUtility x p t

/-- Ex ante expected payment under the type distribution D. -/
@[expose] public noncomputable def expectedPayment (p : Real → Real) (D : TypeDist) : Real :=
  ∫ t, p t ∂D.mu

/-- Ex ante expected virtual surplus under the type distribution D. -/
@[expose] public noncomputable def expectedVirtualSurplus (x : Real → Real) (D : TypeDist) : Real :=
  ∫ t, virtualValue D.F D.f t * x t ∂D.mu

/-- Virtual value unfolds to the type minus the inverse hazard rate. -/
public lemma virtualValue_eq (F f : Real → Real) (t : Real) :
    virtualValue F f t = t - (1 - F t) / f t := by
  rfl

/-- Interim utility is the type-weighted allocation minus the payment. -/
public lemma interimUtility_apply (x p : Real → Real) (t : Real) :
    interimUtility x p t = t * x t - p t := by
  rfl

/-- Bayesian incentive compatibility bounds the utility from every report by truthful utility. -/
public lemma bic_apply (x p : Real → Real) (h : BIC x p) :
    ∀ t r, t * x r - p r ≤ interimUtility x p t := by
  intro t r
  exact h t r

/-- Ex ante expected payment unfolds to the Bochner integral of the payment rule. -/
public lemma expectedPayment_apply (p : Real → Real) (D : TypeDist) :
    expectedPayment p D = ∫ t, p t ∂D.mu := by
  rfl

/-- Expected virtual surplus unfolds to the Bochner integral of virtual value times allocation. -/
public lemma expectedVirtualSurplus_apply (x : Real → Real) (D : TypeDist) :
    expectedVirtualSurplus x D = ∫ t, virtualValue D.F D.f t * x t ∂D.mu := by
  rfl

end MyersonOptimalAuction
