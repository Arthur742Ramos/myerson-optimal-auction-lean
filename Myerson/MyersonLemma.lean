module

public import Myerson.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith

open MeasureTheory

noncomputable section

namespace MyersonOptimalAuction

/-- Bayesian incentive compatibility makes the interim allocation rule monotone. -/
public lemma x_monotone_of_BIC (x p : Real → Real) (h : BIC x p) : Monotone x := by
  intro s t hst
  by_cases heq : s = t
  · subst t
    exact le_rfl
  have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hst heq)
  have hts := bic_apply x p h t s
  have hst_bic := bic_apply x p h s t
  rw [interimUtility_apply] at hts hst_bic
  have hprod : 0 ≤ (t - s) * (x t - x s) := by
    nlinarith [hts, hst_bic]
  have hdiff : 0 ≤ x t - x s := by
    by_contra hnot
    have hneg : x t - x s < 0 := by linarith
    have hprod_neg : (t - s) * (x t - x s) < 0 :=
      mul_neg_of_pos_of_neg hpos hneg
    linarith
  linarith

/-- Under Bayesian incentive compatibility, the utility gap lies between the
type gap times the allocation at the lower and upper types. -/
public lemma bic_sandwich (x p : Real → Real) (h : BIC x p) (s t : Real) (_hst : s ≤ t) :
    ((t - s) * x s ≤ interimUtility x p t - interimUtility x p s) ∧
      (interimUtility x p t - interimUtility x p s ≤ (t - s) * x t) := by
  have hts := bic_apply x p h t s
  have hst_bic := bic_apply x p h s t
  rw [interimUtility_apply] at hts hst_bic
  constructor
  · simp only [interimUtility_apply]
    nlinarith [hts]
  · simp only [interimUtility_apply]
    nlinarith [hst_bic]

/-- Under Bayesian incentive compatibility, the utility difference over an ordered
interval equals the integral of the allocation rule. The proof squeezes utility
and the integral between common finite endpoint sums. -/
public lemma envelope_integral_aux (x p : Real → Real) (hBIC : BIC x p)
    (a b : Real) (hab : a ≤ b) :
    interimUtility x p b - interimUtility x p a = ∫ s in a..b, x s := by
  rcases eq_or_lt_of_le hab with rfl | _hpos
  · simp [intervalIntegral.integral_same]
  have hxmono : Monotone x := x_monotone_of_BIC x p hBIC
  have hxint : ∀ c d : Real, IntervalIntegrable x volume c d :=
    fun _ _ => Monotone.intervalIntegrable hxmono
  suffices hD :
      (interimUtility x p b - interimUtility x p a) -
        (∫ s in a..b, x s) = 0 by
    linarith
  have key : ∀ n : ℕ, 1 ≤ n →
      |(interimUtility x p b - interimUtility x p a) -
        (∫ s in a..b, x s)| ≤ ((b - a) / (n : Real)) * (x b - x a) := by
    intro n hn
    have hnpos : 0 < n := by omega
    have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hnpos
    set q : ℕ → Real := fun i => a + (b - a) * (i : Real) / (n : Real) with hq_def
    have hq0 : q 0 = a := by simp [hq_def]
    have hqn : q n = b := by
      simp only [hq_def]
      rw [mul_div_cancel_right₀ _ (ne_of_gt hnR)]
      ring
    have hqdiff : ∀ i : ℕ, q (i + 1) - q i = (b - a) / (n : Real) := by
      intro i
      have hcast : ((i + 1 : ℕ) : Real) = (i : Real) + 1 := by
        simp
      simp only [hq_def, hcast]
      ring
    have hqle : ∀ i : ℕ, q i ≤ q (i + 1) := by
      intro i
      have hnonneg : 0 ≤ (b - a) / (n : Real) :=
        div_nonneg (sub_nonneg.mpr hab) hnR.le
      linarith [hqdiff i]
    have hsand : ∀ i ∈ Finset.range n,
        ((b - a) / (n : Real)) * x (q i) ≤
          interimUtility x p (q (i + 1)) - interimUtility x p (q i) ∧
        interimUtility x p (q (i + 1)) - interimUtility x p (q i) ≤
          ((b - a) / (n : Real)) * x (q (i + 1)) := by
      intro i _hi
      have h := bic_sandwich x p hBIC (q i) (q (i + 1)) (hqle i)
      rwa [hqdiff i] at h
    have htelU :
        ∑ i ∈ Finset.range n,
          (interimUtility x p (q (i + 1)) - interimUtility x p (q i)) =
        interimUtility x p b - interimUtility x p a := by
      have h := Finset.sum_range_sub (fun i : ℕ => interimUtility x p (q i)) n
      simp only [hqn, hq0] at h
      exact h
    have hUlow :
        ∑ i ∈ Finset.range n, ((b - a) / (n : Real)) * x (q i) ≤
          interimUtility x p b - interimUtility x p a := by
      rw [← htelU]
      exact Finset.sum_le_sum fun i hi => (hsand i hi).1
    have hUhigh :
        interimUtility x p b - interimUtility x p a ≤
          ∑ i ∈ Finset.range n, ((b - a) / (n : Real)) * x (q (i + 1)) := by
      rw [← htelU]
      exact Finset.sum_le_sum fun i hi => (hsand i hi).2
    have hsplit : ∀ i : ℕ,
        (∫ s in a..(q (i + 1)), x s) - (∫ s in a..(q i), x s) =
          ∫ s in (q i)..(q (i + 1)), x s := by
      intro i
      have h := intervalIntegral.integral_add_adjacent_intervals
        (hxint a (q i)) (hxint (q i) (q (i + 1)))
      linarith
    have htelI :
        ∑ i ∈ Finset.range n, (∫ s in (q i)..(q (i + 1)), x s) =
          ∫ s in a..b, x s := by
      have h := Finset.sum_range_sub
        (fun i : ℕ => ∫ s in a..(q i), x s) n
      simp only [hqn, hq0, intervalIntegral.integral_same, sub_zero] at h
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => (hsplit i).symm
    have hconst : ∀ i : ℕ, ∀ c : Real,
        (∫ _ in (q i)..(q (i + 1)), c) = ((b - a) / (n : Real)) * c := by
      intro i c
      rw [intervalIntegral.integral_const, smul_eq_mul, hqdiff i]
    have hint : ∀ i ∈ Finset.range n,
        ((b - a) / (n : Real)) * x (q i) ≤ (∫ s in (q i)..(q (i + 1)), x s) ∧
        (∫ s in (q i)..(q (i + 1)), x s) ≤
          ((b - a) / (n : Real)) * x (q (i + 1)) := by
      intro i _hi
      have h2 : IntervalIntegrable x volume (q i) (q (i + 1)) := hxint _ _
      have hbeta : ∀ c : Real,
          (∫ u in (q i)..(q (i + 1)), (fun _ => c) u) =
            (∫ _ in (q i)..(q (i + 1)), c) := fun _c => rfl
      constructor
      · have hmono : ∀ s ∈ Set.Icc (q i) (q (i + 1)), x (q i) ≤ x s :=
          fun _s hs => hxmono hs.1
        have hle_int := intervalIntegral.integral_mono_on
          (f := fun _ => x (q i)) (g := x) (μ := volume)
          (hqle i) intervalIntegrable_const h2 hmono
        rw [hbeta (x (q i)), hconst i] at hle_int
        exact hle_int
      · have hmono : ∀ s ∈ Set.Icc (q i) (q (i + 1)), x s ≤ x (q (i + 1)) :=
          fun _s hs => hxmono hs.2
        have hle_int := intervalIntegral.integral_mono_on
          (f := x) (g := fun _ => x (q (i + 1))) (μ := volume)
          (hqle i) h2 intervalIntegrable_const hmono
        rw [hbeta (x (q (i + 1))), hconst i] at hle_int
        exact hle_int
    have hIlow :
        ∑ i ∈ Finset.range n, ((b - a) / (n : Real)) * x (q i) ≤
          ∫ s in a..b, x s := by
      rw [← htelI]
      exact Finset.sum_le_sum fun i hi => (hint i hi).1
    have hIhigh :
        (∫ s in a..b, x s) ≤
          ∑ i ∈ Finset.range n, ((b - a) / (n : Real)) * x (q (i + 1)) := by
      rw [← htelI]
      exact Finset.sum_le_sum fun i hi => (hint i hi).2
    have hdiff :
        (∑ i ∈ Finset.range n, ((b - a) / (n : Real)) * x (q (i + 1))) -
          (∑ i ∈ Finset.range n, ((b - a) / (n : Real)) * x (q i)) =
        ∑ i ∈ Finset.range n,
          ((b - a) / (n : Real)) * (x (q (i + 1)) - x (q i)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hfactor :
        ∑ i ∈ Finset.range n,
          ((b - a) / (n : Real)) * (x (q (i + 1)) - x (q i)) =
          ((b - a) / (n : Real)) * (x b - x a) := by
      rw [← Finset.mul_sum]
      congr 1
      have h := Finset.sum_range_sub (fun i : ℕ => x (q i)) n
      simp only [hqn, hq0] at h
      exact h
    rw [← hfactor, ← hdiff, abs_le]
    constructor <;> linarith [hUlow, hUhigh, hIlow, hIhigh]
  have hC : (0 : Real) ≤ x b - x a := sub_nonneg.mpr (hxmono hab)
  by_contra hne
  have hDpos :
      0 < |(interimUtility x p b - interimUtility x p a) -
        (∫ s in a..b, x s)| := abs_pos.mpr hne
  obtain ⟨m, hm⟩ := exists_nat_gt
    ((b - a) * (x b - x a) /
      |(interimUtility x p b - interimUtility x p a) - (∫ s in a..b, x s)|)
  have hratio : 0 ≤ (b - a) * (x b - x a) /
      |(interimUtility x p b - interimUtility x p a) - (∫ s in a..b, x s)| :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hab) hC) hDpos.le
  have hmR : (0 : Real) < (m : Real) := lt_of_le_of_lt hratio hm
  have hmpos : 1 ≤ m := by
    have hmnat : 0 < m := by exact_mod_cast hmR
    omega
  have hle := key m hmpos
  have e1 : (b - a) * (x b - x a) <
      (m : Real) * |(interimUtility x p b - interimUtility x p a) -
        (∫ s in a..b, x s)| := by
    have h := mul_lt_mul_of_pos_right hm hDpos
    rw [div_mul_cancel₀ _ (ne_of_gt hDpos)] at h
    exact h
  have hcancel :
      (((b - a) / (m : Real)) * (x b - x a)) * (m : Real) =
        (b - a) * (x b - x a) := by
    field_simp [ne_of_gt hmR]
  have e2 :
      |(interimUtility x p b - interimUtility x p a) -
        (∫ s in a..b, x s)| * (m : Real) ≤ (b - a) * (x b - x a) := by
    have h := mul_le_mul_of_nonneg_right hle hmR.le
    rw [hcancel] at h
    exact h
  have e3 :
      (m : Real) * |(interimUtility x p b - interimUtility x p a) -
        (∫ s in a..b, x s)| =
      |(interimUtility x p b - interimUtility x p a) -
        (∫ s in a..b, x s)| * (m : Real) := mul_comm _ _
  linarith

/-- Under Bayesian incentive compatibility, utility at every real type equals
utility at the reference type zero plus the oriented allocation integral. -/
public theorem envelope_integral (x p : Real → Real) (hBIC : BIC x p) (t : Real) :
    interimUtility x p t - interimUtility x p 0 = ∫ s in (0 : Real)..t, x s := by
  by_cases ht : 0 ≤ t
  · exact envelope_integral_aux x p hBIC 0 t ht
  · have h := envelope_integral_aux x p hBIC t 0 (le_of_lt (lt_of_not_ge ht))
    rw [intervalIntegral.integral_symm t 0]
    linarith

/-- Bayesian incentive compatibility determines payment from allocation and
utility at the reference type zero. -/
public theorem payment_formula_of_BIC (x p : Real → Real) (hBIC : BIC x p) (t : Real) :
    p t = t * x t - interimUtility x p 0 - ∫ s in (0 : Real)..t, x s := by
  have h := envelope_integral x p hBIC t
  rw [interimUtility_apply x p t] at h
  linarith

/-- A monotone interim allocation rule and the envelope payment formula imply
Bayesian incentive compatibility, using utility at the reference type zero as the
integration constant. -/
public theorem bic_of_monotone_of_payment (x p : Real → Real) (hmono : Monotone x)
    (hpay : ∀ t, p t = t * x t - interimUtility x p 0 -
      ∫ s in (0 : Real)..t, x s) : BIC x p := by
  intro t r
  have hU : ∀ s, interimUtility x p s =
      interimUtility x p 0 + ∫ u in (0 : Real)..s, x u := by
    intro s
    rw [interimUtility_apply, hpay s]
    ring
  have hxint : ∀ a b : Real, IntervalIntegrable x volume a b :=
    fun _ _ => Monotone.intervalIntegrable hmono
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hxint 0 r) (hxint r t)
  have hbound : (t - r) * x r ≤ ∫ s in r..t, x s := by
    by_cases hrt : r ≤ t
    · have hle_int := intervalIntegral.integral_mono_on
        (f := fun _ => x r) (g := x) (μ := volume)
        hrt intervalIntegrable_const (hxint r t)
        (fun _s hs => hmono hs.1)
      simpa only [intervalIntegral.integral_const, smul_eq_mul] using hle_int
    · have htr : t ≤ r := le_of_lt (lt_of_not_ge hrt)
      have hle_int := intervalIntegral.integral_mono_on
        (f := x) (g := fun _ => x r) (μ := volume)
        htr (hxint t r) intervalIntegrable_const
        (fun _s hs => hmono hs.2)
      simp only [intervalIntegral.integral_const, smul_eq_mul] at hle_int
      rw [intervalIntegral.integral_symm t r]
      nlinarith [hle_int]
  rw [hpay r, hU t]
  nlinarith [hadd, hbound]

/-- Myerson's lemma: Bayesian incentive compatibility is equivalent to monotone
interim allocation and the envelope payment formula at the reference type zero. -/
public theorem myersonLemma (x p : Real → Real) :
    BIC x p ↔ Monotone x ∧ ∀ t,
      p t = t * x t - interimUtility x p 0 - ∫ s in (0 : Real)..t, x s := by
  constructor
  · intro hBIC
    exact ⟨x_monotone_of_BIC x p hBIC, payment_formula_of_BIC x p hBIC⟩
  · rintro ⟨hmono, hpay⟩
    exact bic_of_monotone_of_payment x p hmono hpay

end MyersonOptimalAuction
