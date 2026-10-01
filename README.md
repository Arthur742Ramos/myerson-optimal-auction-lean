# Myerson's Optimal Auction Theorem (Lean 4)

A Lean 4 + Mathlib formalization of Myerson's 1981 optimal auction design
theorem, **regular case** (virtual values nondecreasing on nonnegative types;
ironing for irregular distributions is out of scope). It is a companion to the
[revenue-equivalence](https://github.com/Arthur742Ramos/revenue-equivalence-lean)
formalization (Palomar `PALOMAR-2026-10-01-000011`), whose BIC/envelope
approach the interim machinery here follows.

## Model (M1, `Myerson/Dist.lean`, `Myerson/Defs.lean`)

Each bidder's prior is a `TypeDist`: a probability measure `mu : Measure Real`
with a continuous monotone CDF `F : Real → Real` satisfying
`F t = (mu (Set.Iic t)).toReal`, and a measurable nonnegative Lebesgue density
`f` with `mu s = ENNReal.ofReal (∫ t in s, f t ∂volume)`. The density vanishes
for negative types (`f_eq_zero_of_neg`) and the CDF vanishes at nonpositive
types (`F_eq_zero_of_nonpos`), so each prior's mass lies on `[0, ∞)`. Types
are still modeled over all of `ℝ`: there is no lowest type.

- Virtual value: `MyersonOptimalAuction.virtualValue (F f : Real → Real)
  (t : Real) : Real := t - (1 - F t) / f t`.
- Regularity: `MyersonOptimalAuction.Regular {n : Nat} (D : Fin n → TypeDist)
  : Prop := ∀ i, MonotoneOn (fun t => virtualValue (D i).F (D i).f t)
  (Set.Ici 0)` — every bidder's virtual value is nondecreasing on
  nonnegative types (the type space). Regularity is deliberately *not*
  global monotonicity over all of `ℝ`: the global version is vacuous (no
  `TypeDist` satisfies it together with `hsupp`), see the M9 note below.
- Interim rules `x p : Real → Real`; interim utility
  `interimUtility x p t = t * x t - p t` (quasi-linear).
- `BIC x p := ∀ t r, t * x r - p r ≤ interimUtility x p t`: truthful reporting
  maximizes interim utility.
- `IIR x p := ∀ t, 0 ≤ interimUtility x p t`: quantified over all real types.
- `expectedPayment p D = ∫ t, p t ∂D.mu` and
  `expectedVirtualSurplus x D = ∫ t, virtualValue D.F D.f t * x t ∂D.mu`:
  both are Bochner integrals, hence totalized (they return `0` for
  nonintegrable integrands). Every expectation claim in this development
  carries the integrability hypotheses that make it non-vacuous.

## Myerson's lemma (M2, `Myerson/MyersonLemma.lean`)

`MyersonOptimalAuction.myersonLemma (x p : Real → Real) : BIC x p ↔
Monotone x ∧ ∀ t, p t = t * x t - interimUtility x p 0 -
∫ s in (0:Real)..t, x s`. BIC holds iff the interim allocation is monotone
and payments follow the envelope formula, with `interimUtility x p 0` the
interim utility at the reference type (type zero) — not assumed to be zero.

## Virtual-surplus identity (M3, `Myerson/VirtualSurplus.lean`)

`MyersonOptimalAuction.virtualSurplusIdentity` proves, under
`hBIC : BIC x p`, the support hypothesis
`hsupp : ∀ t : Real, 0 < t → 0 < D.F t` (with `F` the CDF and `F 0 = 0`
proved, this says the prior puts positive mass in `(0, t]` for every
`t > 0`: zero is in the support, i.e. there is mass arbitrarily close to
zero from above), and the five integrability hypotheses
`Integrable p D.mu`, `Integrable (fun t => t * x t) D.mu`,
`Integrable (fun t => ∫ s in (0:Real)..t, x s) D.mu`,
`Integrable (fun s => x s * (1 - D.F s)) volume`, and
`Integrable (fun t => virtualValue D.F D.f t * x t) D.mu`, that

```
expectedPayment p D = expectedVirtualSurplus x D - interimUtility x p 0.
```

The support hypothesis is sharp. The following is a hand-checked example
(all numbers verified by hand; it is not formalized in Lean): take `D`
uniform on `[1,2]` as a `TypeDist` (`hsupp` fails, since `F = 0` on
`(0,1)`); `x(s) = 0` for `s ≤ 0`, `x(s) = s` for `0 ≤ s ≤ 1`, `x(s) = 1`
for `s ≥ 1` (monotone, continuous); and `p(t) = t * x(t) - ∫₀ᵗ x(s) ds`,
i.e. `p = 0` on `(-∞, 0]`, `p(t) = t²/2` on `[0,1]`, `p(t) = 1/2` on
`[1,∞)`. Then `(x, p)` is BIC (`x` monotone plus the envelope formula with
`U(0) = 0`), and all five integrability hypotheses hold: `p` is bounded;
`t * x(t)` is bounded on the support `[1,2]`; `∫₀ᵗ x` is bounded on
`[1,2]`; `x(s) * (1 - F(s))` equals `0` on `(-∞,0]`, `s` on `[0,1]`,
`2 - s` on `[1,2]`, `0` on `[2,∞)` — continuous with compact support,
hence integrable over `ℝ` (its integral is `1`); and
`virtualValue * x` is bounded on `[1,2]`. But the identity's conclusion
fails: `E[p] = 1/2` while `E[virtualValue * x] - U(0) = 1 - 0 = 1` (on
`(1,2)`, `virtualValue(t) = 2t - 2`, and `∫₁² (2t-2) dt = 1`). The
integrability hypotheses are load-bearing: without them Lean's totalized
Bochner integral makes the equality vacuous.

## Optimal auction theorem (M4, `Myerson/FubiniCoord.lean`, `Myerson/OptimalAuction.lean`)

`Myerson.optimalAuction {n : Nat} (D : Fin n → TypeDist) (hn : 0 < n)`:
with `hreg : Regular D`, the support hypothesis
`hsupp : ∀ i (t : Real), 0 < t → 0 < (D i).F t`, and the integrability
hypotheses `∀ i, Integrable (fun t : Real => t) (D i).mu`,
`∀ i, Integrable (fun t : Real => virtualValue (D i).F (D i).f t) (D i).mu`,
and `∀ i, Integrable (fun s => optInterim D hn i s * (1 - (D i).F s)) volume`:
for every ex post allocation `X : Fin n → (Fin n → Real) → Real` with
`∀ i, Measurable (X i)`, `∀ i t, 0 ≤ X i t`, and pointwise feasibility
`∀ t, ∑ i, X i t ≤ 1` (at most one item at every type profile), and every
interim payment profile `p : Fin n → Real → Real` with
`∀ i, BIC (interimAlloc D X i) (p i)`,
`∀ i, IIR (interimAlloc D X i) (p i)`,
`∀ i, Integrable (p i) (D i).mu`, and
`∀ i, Integrable (fun s => interimAlloc D X i s * (1 - (D i).F s)) volume`,
the conclusion is

```
(∀ i, BIC (optInterim D hn i) (optPayment D hn i)) ∧
(∀ i, IIR (optInterim D hn i) (optPayment D hn i)) ∧
∑ i, expectedPayment (p i) (D i) ≤
  ∑ i, expectedPayment (optPayment D hn i) (D i).
```

Independence is the product measure `Myerson.jointMu D :=
Measure.pi fun j => (D j).mu` over type profiles `Fin n → Real`; the interim
allocation `Myerson.interimAlloc D X i s := ∫ t, X i (Function.update t i s)
∂(jointMu D)` integrates the ex post rule over the other bidders' types with
bidder `i`'s type fixed at `s` (the coordinate Fubini machinery is
`Myerson.fubini_coord`).

The mechanism: `Myerson.maxVirt D hn t` is the largest virtual value at
profile `t`; `Myerson.attainers` is the finset of bidders attaining it;
`Myerson.winner D hn t` is the least bidder index among the attainers
(deterministic, measurable tie-breaking); `Myerson.optAlloc D hn i` is the
indicator of `{t | 0 < maxVirt D hn t ∧ winner D hn t = i}` — the item goes
to the winner iff the highest virtual value is strictly positive, and there
is no sale otherwise. Payments are the envelope payments
`Myerson.optPayment D hn i t = t * optInterim D hn i t -
∫ s in (0:Real)..t, optInterim D hn i s`, normalized so that
`interimUtility (optInterim D hn i) (optPayment D hn i) 0 = 0`
(`optUtil_zero`).

## Regularity repair and non-vacuity witness (M9, `Myerson/Examples.lean`)

An earlier version stated regularity as *global* monotonicity of virtual
values over all of `ℝ`
(`∀ i, Monotone fun t => virtualValue (D i).F (D i).f t`). That statement is
vacuous, and the vacuity is real, not a technicality. For `t < 0` the
density vanishes (`f_eq_zero_of_neg`), so with Lean's totalized division
`virtualValue t = t - (1 - F t) / 0 = t`. Global monotonicity then forces
`vv(0) ≥ sup_{t<0} t = 0`; but `vv(0) = 0 - (1 - 0) / f(0) = -1 / f(0)`,
so `f(0) = 0` and `vv(0) = 0`, hence `vv(t) ≥ 0` for every `t > 0`. With
`hsupp`, continuity, and `F(0) = 0`, for small `t > 0` we get
`0 < F(t) < 1/2`, so `pos_of_interior` gives `f(t) > 0` and `vv(t) ≥ 0`
forces `f(t) ≥ (1 - F(t)) / t > 1 / (2t)` — whose integral over `(0, δ)`
diverges, contradicting the finite-mass density (`integrable_f`,
integral `1`). No `TypeDist` satisfies global regularity together with
`hsupp`.

The repaired definition restricts monotonicity to nonnegative types
(`MonotoneOn ... (Set.Ici 0)`), the standard notion: Myerson regularity is
monotonicity of virtual values on the type space `[0, ∞)`. The one proof
that used global monotonicity, `optAlloc_mono_update`, is repaired by a
case split: a bidder with a negative own-type has negative virtual value
(`optAlloc_eq_zero_of_neg`), hence never wins, so the allocation there is
`0 ≤` anything; on `0 ≤ s ≤ s'` the `MonotoneOn` hypothesis applies
directly.

`Myerson/Examples.lean` exhibits
`MyersonOptimalAuction.uniform01`, the uniform distribution on `[0,1]` as
a `TypeDist`, and proves `MyersonOptimalAuction.uniform01_qualifies`: it
is regular in the repaired sense (`uniform01_regular`), satisfies `hsupp`
(`uniform01_hsupp`), and has integrable identity and virtual-value
functions (`uniform01_integrable_id`, `uniform01_integrable_vv`). Its
virtual values are `min (2t-1) t` on `[0,∞)` (`uniform01_vv`): `2t - 1`
on `[0,1]`, `t` above `1`, and `vv(0) = -1 < 0` — a negative virtual value
at zero is exactly what global monotonicity could not tolerate. The
optimal-auction theorem's hypotheses are jointly satisfiable.

## Palomar packaging (M5)

`Challenge.lean` declares `MyersonOptimalAuction.Palomar.virtualSurplusIdentity`
and `MyersonOptimalAuction.Palomar.optimalAuction` with the exact library
binders above (2 deliberate sorries, the statement placeholders);
`Solution.lean` restates both names and proves them by applying the library
theorems. `comparator.json` names the 2 theorems and 6 genuine definitions
(`virtualValue`, `Regular`, `interimUtility`, `BIC`, `IIR`, `expectedPayment`).

## Verification (M7)

`scripts/verify-palomar.sh` passes (exit 0); the official `lake comparator`
stage reports "Your solution is okay!".

## Quality bar

Zero sorries in the library (`Myerson/`) and `Solution.lean`; axioms
contained in `{propext, Classical.choice, Quot.sound}`; every prose claim in
this file is backed by the exact Lean declaration quoted next to it.
