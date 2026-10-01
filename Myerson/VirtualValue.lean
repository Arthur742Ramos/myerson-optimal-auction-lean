module

public import Myerson.Defs
public import Myerson.Dist

open MeasureTheory

namespace MyersonOptimalAuction

/-- Multiplying virtual value by a nonzero density clears the inverse hazard rate. -/
public lemma virtualValue_mul_density (F f : Real → Real) (t : Real) (hf : f t ≠ 0) :
    virtualValue F f t * f t = t * f t - (1 - F t) := by
  rw [virtualValue_eq, sub_mul, div_mul_cancel₀ _ hf]

/-- Measurable CDF and density functions give a measurable virtual value function. -/
public lemma measurable_virtualValue {F f : Real → Real} (hF : Measurable F) (hf : Measurable f) :
    Measurable (virtualValue F f) := by
  unfold virtualValue
  exact measurable_id.sub ((measurable_const.sub hF).div hf)

end MyersonOptimalAuction

namespace TypeDist

/-- The virtual value of a type distribution is measurable. -/
public lemma measurable_virtualValue (D : TypeDist) :
    Measurable fun t => MyersonOptimalAuction.virtualValue D.F D.f t :=
  MyersonOptimalAuction.measurable_virtualValue D.F_measurable D.f_measurable

/-- Positive density in the CDF interior allows cancellation in the virtual value formula. -/
public lemma virtualValue_mul_density (D : TypeDist) (t : Real) (h0 : 0 < D.F t) (h1 : D.F t < 1) :
    MyersonOptimalAuction.virtualValue D.F D.f t * D.f t = t * D.f t - (1 - D.F t) :=
  MyersonOptimalAuction.virtualValue_mul_density D.F D.f t
    (ne_of_gt (D.pos_of_interior t h0 h1))

end TypeDist
