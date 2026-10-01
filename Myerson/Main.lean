import Myerson.Dist
import Myerson.Defs
import Myerson.VirtualValue

/-
Myerson's 1981 optimal auction design theorem, formalized in Lean 4.

Milestone plan:
  M1  DONE. Model: type distributions, virtual values, regularity.
  M2  Myerson's lemma: BIC iff monotone interim allocation + envelope payments
      (adapted from the revenue-equivalence development).
  M3  Virtual surplus identity: expected payment equals expected virtual
      surplus minus base utility.
  M4  Optimal auction theorem: allocating to the highest nonnegative virtual
      value maximizes expected revenue over BIC + interim-IR mechanisms
      (regular case; no ironing).
  M5  Palomar Challenge/Solution packaging.
  M6  Prose audit (formalization.yaml, README) against the exact Lean binders.
  M7  Local Palomar verifier replica.
-/
