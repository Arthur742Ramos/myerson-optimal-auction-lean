# Myerson's Optimal Auction Theorem (Lean 4)

A Lean 4 + Mathlib formalization of Myerson's 1981 optimal auction design
theorem, following the Palomar packaging pattern used in the
[revenue-equivalence](https://github.com/Arthur742Ramos/revenue-equivalence-lean)
development.

## Scope

Single-parameter independent-private-values environment: finitely many
bidders, independent continuous type distributions, risk-neutral bidders.
The formalization covers the **regular case** (nondecreasing virtual values);
ironing for irregular distributions is out of scope and is stated as such in
`formalization.yaml`.

## Milestones

- **M1** — Model: type distributions, virtual values
  `ψ(t) = t - (1 - F(t)) / f(t)`, regularity.
- **M2** — Myerson's lemma: BIC iff monotone interim allocation and envelope
  payments (adapted from the revenue-equivalence library).
- **M3** — Virtual surplus identity: expected payment equals expected virtual
  surplus minus the base utility.
- **M4** — Optimal auction theorem: allocating to the highest nonnegative
  virtual value maximizes expected revenue over all BIC and interim-IR
  mechanisms.
- **M5** — Palomar `Challenge.lean` / `Solution.lean` packaging.
- **M6** — Prose audit of `formalization.yaml` and this README against the
  exact Lean binders.
- **M7** — Local Palomar verifier replica (`scripts/verify-palomar.sh`).

## Quality bar

Zero sorries in the library and `Solution.lean`; axioms contained in
`{propext, Classical.choice, Quot.sound}`; every prose claim backed by an
exact Lean declaration.
