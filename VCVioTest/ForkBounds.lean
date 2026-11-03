/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.ReplayFork
public import VCVio.CryptoFoundations.SeededFork

/-!
# External canaries for the forking bounds

These examples deliberately live outside the defining modules. They lock the public hypotheses and
result shapes of the seeded and replay forking bounds, so changes to either cannot silently make
them unusable by downstream crypto proofs.
-/

public section

open MeasureTheory OracleSpec ENNReal Finset

namespace VCVioTest.ForkBounds

section seeded

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α : Type}
  [OracleSpec.UniformAnswerMeasure spec]

/-- The seeded forking bound remains directly consumable from another module. -/
example (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    [∀ j, SampleableType (spec.Range j)] [∀ j, DecidableEq (spec.Range j)]
    [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec] [Fintype (spec.Range i)] :
    ((∑ s, Pr{let x ← main}[cf x = some s]) ^ 2 / ((qb i + 1 : ℕ) : ℝ≥0∞)
        - (∑ s, Pr{let x ← main}[cf x = some s]) /
            ((Fintype.card (spec.Range i) : ℕ) : ℝ≥0∞)) ≤
      Pr{let r ← OracleComp.seededFork main qb js i cf}[r.isSome] :=
  OracleComp.le_prEvent_isSome_seededFork_sq main qb js i cf

end seeded

section replay

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α : Type}
  [OracleSpec.UniformAnswerMeasure spec]

/-- The replay forking bound retains its reachability premise and success-event shape. -/
example [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι) [Fintype (spec.Range i)]
    (cf : α → Option (Fin (qb i + 1)))
    (hreach : OracleComp.PathCfReachable main qb i cf) :
    (let acc : ℝ≥0∞ := ∑ s, Pr{let x ← main}[cf x = some s]
     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
     let q := qb i + 1
     acc * (acc / q - h⁻¹)) ≤
      Pr{let r ← OracleComp.contextFork main qb i cf}[r.isSome] :=
  OracleComp.le_prEvent_isSome_contextFork main qb i cf hreach

end replay

section replayMixed

variable {ι ι' : Type} [DecidableEq ι] [DecidableEq ι'] {coins : OracleSpec ι'}
  {spec : OracleSpec ι} {α : Type} [OracleSpec.AnswerMeasure coins]
  [OracleSpec.UniformAnswerMeasure spec]

/-- The replay forking bound needs uniform answers only at the forked query. Here the fork is at a
query of the uniform summand `spec` while the summand `coins` carries arbitrary answer measures,
and the uniformity instance at the forked query is found through
`OracleSpec.UniformAnswerMeasureAt.add_inr`. -/
example [∀ t, DecidableEq ((coins + spec).Range t)]
    (main : OracleComp (coins + spec) α) (qb : ι' ⊕ ι → ℕ) (i : ι)
    [Fintype ((coins + spec).Range (Sum.inr i))]
    (cf : α → Option (Fin (qb (Sum.inr i) + 1)))
    (hreach : OracleComp.PathCfReachable main qb (Sum.inr i) cf) :
    (let acc : ℝ≥0∞ := ∑ s, Pr{let x ← main}[cf x = some s]
     let h : ℝ≥0∞ := Fintype.card ((coins + spec).Range (Sum.inr i))
     let q := qb (Sum.inr i) + 1
     acc * (acc / q - h⁻¹)) ≤
      Pr{let r ← OracleComp.contextFork main qb (Sum.inr i) cf}[r.isSome] :=
  OracleComp.le_prEvent_isSome_contextFork main qb (Sum.inr i) cf hreach

end replayMixed

end VCVioTest.ForkBounds
