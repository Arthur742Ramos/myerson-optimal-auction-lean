# Myerson's Optimal Auction Theorem (Lean 4)

A Lean 4 + Mathlib formalization of Myerson's 1981 optimal auction design
theorem, **regular case** (nondecreasing virtual values; ironing for irregular
distributions is out of scope). It is a companion to the
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
  : Prop := ∀ i, Monotone fun t => virtualValue (D i).F (D i).f t` — every
  bidder's virtual value is nondecreasing in their own type.
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
`hsupp : ∀ t : Real, 0 < t → 0 < D.F t` (the distribution puts positive mass
above every positive type), and the five integrability hypotheses
`Integrable p D.mu`, `Integrable (fun t => t * x t) D.mu`,
`Integrable (fun t => ∫ s in (0:Real)..t, x s) D.mu`,
`Integrable (fun s => x s * (1 - D.F s)) volume`, and
`Integrable (fun t => virtualValue D.F D.f t * x t) D.mu`, that

```
expectedPayment p D = expectedVirtualSurplus x D - interimUtility x p 0.
```

The support hypothesis is sharp: a constant unit allocation with zero
payments under a uniform `[1,2]` prior satisfies BIC and all integrability
hypotheses, yet has expected payment `0` while expected virtual surplus minus
reference utility is `1`. The integrability hypotheses are load-bearing:
without them Lean's totalized Bochner integral makes the equality vacuous.

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
