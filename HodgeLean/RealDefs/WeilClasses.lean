import HodgeLean.RealDefs.AbelianExterior
import HodgeLean.Blocks.Weil.KernelIdentity

/-! # Weil classes of a real abelian variety, against upstream's `Hdg^p`

Phase 4 Task 2 (`docs/briefs/weil.md`).

Throughout, `X` is abelian (`[GrpObj X]`), `S := abelianVarietyCohomologyOf hF hB hD hT` is its
Blocks package, `A : HodgeBlocks.WeilAction S.weight1 d` is a Weil action on `H¹(X(ℂ); ℚ)`,
`hW : A.IsWeilType`, and `k := finrank ℂ (A.Vs ⊓ S.weight1.H (1, 0))`.

**Where `J` comes from.** A Weil action is a rational endomorphism `J` of `H¹(X(ℂ); ℚ)`, with
`J² = −d`, that preserves the Hodge pieces of `H¹`. Such endomorphisms are exactly `End⁰(X)`
acting on `H¹` (Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Ch. 1, the
analytic and rational representations of `End⁰(X)`). That identification is not formalized: here
`A` is any such endomorphism of the cohomology, not an endomorphism of `X`.

* `h10_sup_h01_eq_top`: `H^{1,0} ⊔ H^{0,1} = ℂ ⊗ H¹`, under C1, C2 and C4.
* `weilClassOf A hW`: the rational Weil classes, carried to `H^(2k)(X(ℂ); ℚ)` by the cup product.
* `weilClassOf_le_hdg`: Weil's theorem against upstream's `Hdg^k`, under C1, C2, C4, C7 and O5.
* `two_mul_finrank_vs_inf_h10_eq`: `2k = dim X` for a Weil-type action with `d > 0`.
* `WeilClassesAlgebraic A hW`: F-1569's claim for `X`, that every rational Weil class is algebraic.
  It is a definition, stated and not proved.
* `divisorWeilSpan A hW` and the hypothesis `HodgeRingGeneratedByDivisorsAndWeil A hW`: the
  smallest cup-closed family containing `1`, `Hdg¹` and the Weil classes, and the hypothesis that
  it contains every Hodge class.
* `hdg_le_span_of_weilClassesAlgebraic`: the connector. Weil classes algebraic, plus generation,
  plus C9 and Lefschetz (1,1), give the Hodge conjecture for `X`.
-/

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open scoped TensorProduct

namespace HodgeLean.RealDefs

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
variable {μ : CupProduct X} [GrpObj X]

section WeightOne

omit [GrpObj X] in
/-- The weight-one Hodge structure of `H¹(X(ℂ); ℚ)` is the sum of its `(1, 0)` and `(0, 1)`
pieces. Its pieces cover `ℂ ⊗ H¹` (C4, `isInternal`); off the line `p + q = 1` they are `⊥`
(`supported`), and on it every piece other than `(1, 0)` and `(0, 1)` has `p > 1` or `q > 1`, so
upstream's `hodgePiece` vanishes there (U4, `hodgePiece_eq_bot_of_lt`). -/
theorem cohomologyHodgeStructure_one_h10_sup_h01 (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) :
    letI := hF.finite 1
    (cohomologyHodgeStructure hF hB hD 1).H (1, 0) ⊔
      (cohomologyHodgeStructure hF hB hD 1).H (0, 1) = ⊤ := by
  let := hF.finite 1
  have hbot : ∀ p q : ℤ, (p, q) ≠ (1, 0) → (p, q) ≠ (0, 1) →
      cohomologyHodgePiece X 1 (p, q) = ⊥ := by
    intro p q h10 h01
    rw [congrFun (cohomologyHodgePiece_eq_map hB 1) (p, q), deRhamHodgePiece]
    split_ifs with h
    · simp only [ne_eq, Prod.mk.injEq, not_and] at h10 h01
      rw [hodgePiece_eq_bot_of_lt X (by push_cast at h ⊢; omega), Submodule.map_bot]
    · exact Submodule.map_bot _
  refine eq_top_iff.mpr ?_
  rw [← (cohomologyHodgeStructure hF hB hD 1).isInternal.submodule_iSup_eq_top]
  refine iSup_le fun pq => ?_
  obtain ⟨p, q⟩ := pq
  by_cases h10 : (p, q) = ((1 : ℤ), (0 : ℤ))
  · rw [h10]
    exact le_sup_left
  by_cases h01 : (p, q) = ((0 : ℤ), (1 : ℤ))
  · rw [h01]
    exact le_sup_right
  rw [cohomologyHodgeStructure_H, hbot p q h10 h01]
  exact bot_le

/-- **`H^{1,0} ⊔ H^{0,1} = ℂ ⊗ H¹` for the package (C1, C2, C4).** The hypothesis `hH` that Blocks'
`weilClasses` takes, for `S.weight1`, which is `cohomologyHodgeStructure hF hB hD 1`
(`cohomologyHodgeStructure_one_h10_sup_h01`). `hT` only fixes the package; the statement does not
use the torus theorem. -/
theorem h10_sup_h01_eq_top (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) :
    letI := hT.finite
    (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0) ⊔
      (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (0, 1) = ⊤ :=
  cohomologyHodgeStructure_one_h10_sup_h01 hF hB hD

end WeightOne

section WeilClasses

/-- **The rational Weil classes of `X`, in `H^(2k)(X(ℂ); ℚ)`.** The image of Blocks'
`A.weilClasses` (the rational classes of `⋀^(k + k) H¹` whose complexification lies in the span of
the two top lines `⋀^top Vs` and `⋀^top Vsbar`) under the cup product `cupWedgeMap (k + k)`, read in
`H^(2k)` along `k + k = 2k` (`HQ.castEquiv`).

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism `J` of `H¹` with `J² = −d` that
preserves the Hodge pieces. Such endomorphisms are exactly `End⁰(X)` acting on `H¹`
(Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Ch. 1, the analytic and
rational representations of `End⁰(X)`); that identification is not formalized, so `A` need not
come from an endomorphism of `X`. -/
noncomputable def weilClassOf (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) :
    letI := hT.finite
    Submodule ℚ (HQ X (2 * Module.finrank ℂ
      ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)))) :=
  letI := hT.finite
  (A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hW).map
    ((HQ.castEquiv X (two_mul _).symm).toLinearMap ∘ₗ μ.cupWedgeMap _)

/-- **Weil classes are Hodge classes, against upstream's `Hdg^k` (Weil's theorem).** For an abelian
`X` with a Weil-type action `A` on `H¹(X(ℂ); ℚ)`, every rational Weil class `weilClassOf A hW` lies
in upstream's `Hdg^k(X; ℚ)`, `k = finrank ℂ (Vs ⊓ H^{1,0})`. Blocks'
`isHodgeClass_of_mem_weilClasses` makes it a Hodge class of the exterior power of `H¹`, and
`isHodgeClass_exteriorPower_add_iff` (the exterior power is the cohomology, under O5) carries that
to `Hdg^k`.

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism of `H¹` that preserves the Hodge
pieces. Such endomorphisms are exactly `End⁰(X)` acting on `H¹`; that identification is not
formalized, so the theorem covers every such endomorphism of the cohomology, whether or not it
comes from `X`.

Source: Weil, "Abelian varieties and the Hodge ring" (1977), as in the source line of Blocks' `WeilClassesAreHodge` (paper level; proved here through Blocks' `isHodgeClass_of_mem_weilClasses`); Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 (through `TorusCohomology`), with Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76, §7.1 (through `CupFiltered`).

| hypothesis | roadmap |
| --- | --- |
| `hF : FiniteBetti X` | C1 |
| `hB : BettiDeRhamIso X` | C2 |
| `hD : HodgeDecomposition X` | C4 |
| `hT : TorusCohomology μ` | C7 |
| `hC : CupFiltered X μ` | O5 |
| `A : WeilAction S.weight1 d` | the Weil action (data, not a hypothesis of `X`) |
| `hW : A.IsWeilType` | the action is of Weil type |

Relation to the goal: HC no distance; AV milestone no distance (it says the Weil classes are Hodge
classes, the half of the Weil-class question that is a theorem; algebraicity is
`WeilClassesAlgebraic`, which is not proved). -/
@[hodge_milestone] theorem weilClassOf_le_hdg (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hC : CupFiltered X μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) :
    letI := hT.finite
    weilClassOf hF hB hD hT A hW ≤ Hdg^(Module.finrank ℂ
      ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)))(X; ℚ) := by
  let := hT.finite
  rintro _ ⟨w, hw, rfl⟩
  exact (isHodgeClass_exteriorPower_add_iff hF hB hD hT hC _ w).mp
    (A.isHodgeClass_of_mem_weilClasses (h10_sup_h01_eq_top hF hB hD hT) hW hw)

/-- **`2k = dim X` for a Weil-type action.** With `k = finrank ℂ (Vs ⊓ H^{1,0})`:
`Vs ⊕ Vsbar = ℂ ⊗ H¹` (`isCompl_Vs_Vsbar`, from `J² = −d` with `d > 0`), `dim Vs = dim Vsbar`
(conjugation, `finrank_Vsbar_eq_Vs`), `dim H¹ = 2 · dim X` (C7, `TorusCohomology.finrank_eq`), and
`IsWeilType` is `2k = dim Vs`. So `dim Vs = dim X` and `2k = dim X`. The Weil classes therefore
sit in `H^(2k) = H^(dim X)`, the middle degree, and a Weil-type action forces `dim X` even.

`hd : 0 < d` is a hypothesis because `WeilAction` does not carry it. For `d ≤ 0`, `omegaC d = 0`,
so `Vs = Vsbar = ker J`, and the two eigenspaces need not span.

`hF`, `hB` and `hD` only fix the package `S`, whose `weight1` the action lives on; the count uses
the torus theorem (C7) for `dim H¹`.

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism of `H¹` preserving the Hodge
pieces, which is `End⁰(X)` acting on `H¹` (Birkenhake–Lange, Ch. 1); that identification is not
formalized. -/
theorem two_mul_finrank_vs_inf_h10_eq (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ} (hd : 0 < d)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) :
    letI := hT.finite
    2 * Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) =
      dim X.left := by
  let := hT.finite
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A.Vs A.Vsbar
  have hc := HodgeBlocks.WeilAction.isCompl_Vs_Vsbar A hd
  rw [hc.sup_eq_top, hc.inf_eq_bot, finrank_top, finrank_bot, add_zero,
    Module.finrank_baseChange, hT.finrank_eq, A.finrank_Vsbar_eq_Vs] at hsum
  have hw : 2 * _ = _ := hW
  omega

/-- A Weil-type action (with `d > 0`) forces `dim X` to be even. -/
example (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) {d : ℚ} (hd : 0 < d)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) :
    Even (dim X.left) :=
  ⟨_, (two_mul_finrank_vs_inf_h10_eq hF hB hD hT hd A hW).symm.trans (two_mul _)⟩

/-- For an abelian fourfold, `k = 2`: the Weil classes lie in `H⁴`, and `weilClassOf_le_hdg` puts
them in `Hdg²`. -/
example (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) {d : ℚ} (hd : 0 < d)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) (hg : dim X.left = 4) :
    letI := hT.finite
    Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) = 2 := by
  have := two_mul_finrank_vs_inf_h10_eq hF hB hD hT hd A hW
  omega

/-- For an abelian sixfold, `k = 3`: the Weil classes lie in `H⁶`, and `weilClassOf_le_hdg` puts
them in `Hdg³`. -/
example (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) {d : ℚ} (hd : 0 < d)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) (hg : dim X.left = 6) :
    letI := hT.finite
    Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) = 3 := by
  have := two_mul_finrank_vs_inf_h10_eq hF hB hD hT hd A hW
  omega

/-- **The rational Weil classes of `X` are algebraic** (F-1569's claim for one `X`): every element of
`weilClassOf A hW` lies in `algebraicCycleClassSpan X k`. It is about **every** rational Weil class
of the action `A`, not one chosen class, and not every Hodge class of `X`.

F-1569's claim is this statement when `(X, A)` is a member of `M = (3, ℚ(√−3), [−2])` with
its `ℚ(√−3)`-action; for any other `X` or action it is not F-1569.

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism of `H¹` preserving the Hodge
pieces, which is `End⁰(X)` acting on `H¹` (Birkenhake–Lange, Ch. 1); that identification is not
formalized.

**This is stated, not proved; nothing in this repository proves it.** It is a definition, used as a
premise: every theorem that takes it says so in its hypothesis table.

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism of `H¹` that preserves the Hodge
pieces. Such endomorphisms are exactly `End⁰(X)` acting on `H¹` (Birkenhake–Lange, *Complex Abelian
Varieties*, 2nd ed., Grundlehren 302, Ch. 1); that identification is not formalized. -/
def WeilClassesAlgebraic (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) : Prop :=
  letI := hT.finite
  weilClassOf hF hB hD hT A hW ≤ algebraicCycleClassSpan X (Module.finrank ℂ
    ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)))

/-- A family `F p ⊆ H^(2p)(X(ℂ); ℚ)` that contains the unit in degree `p = 0`, `Hdg¹(X; ℚ)` in
degree `p = 1` and the rational Weil classes `weilClassOf A hW` in degree `p = k`, and is closed
under cup product (`a ∈ F p`, `b ∈ F q` give `a ∪ b ∈ F (p + q)`).

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism of `H¹` preserving the Hodge
pieces, which is `End⁰(X)` acting on `H¹` (Birkenhake–Lange, Ch. 1); that identification is not
formalized. -/
structure IsDivisorWeilClosed (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) (F : ∀ p : ℕ, Submodule ℚ (HQ X (2 * p))) : Prop where
  unit_mem : (show HQ X (2 * 0) from unitClass X) ∈ F 0
  hdg_one_le : Hdg^1(X; ℚ) ≤ F 1
  weil_le : letI := hT.finite
    weilClassOf hF hB hD hT A hW ≤ F (Module.finrank ℂ
      ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)))
  cup_mem : ∀ {p q : ℕ} (h : 2 * p + 2 * q = 2 * (p + q)) (a : HQ X (2 * p)) (b : HQ X (2 * q)),
    a ∈ F p → b ∈ F q → μ.cup h a b ∈ F (p + q)

/-- **The subring generated by divisors and Weil classes.** `divisorWeilSpan A hW p` is the
degree-`2p` part of the smallest family containing `1`, `Hdg¹(X; ℚ)` and `weilClassOf A hW` and
closed under cup product: the infimum, degree by degree, of every `IsDivisorWeilClosed` family.

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism of `H¹` preserving the Hodge
pieces, which is `End⁰(X)` acting on `H¹` (Birkenhake–Lange, Ch. 1); that identification is not
formalized. -/
noncomputable def divisorWeilSpan (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) (p : ℕ) : Submodule ℚ (HQ X (2 * p)) :=
  ⨅ (F : ∀ p : ℕ, Submodule ℚ (HQ X (2 * p))) (_ : IsDivisorWeilClosed hF hB hD hT A hW F), F p

section DivisorWeilSpan

variable (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
  (hT : TorusCohomology μ) {d : ℚ}
  (A : letI := hT.finite
    HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
  (hW : letI := hT.finite; A.IsWeilType)

/-- `divisorWeilSpan` lies in every family that contains the generators and is cup-closed. -/
theorem divisorWeilSpan_le {F : ∀ p : ℕ, Submodule ℚ (HQ X (2 * p))}
    (hFc : IsDivisorWeilClosed hF hB hD hT A hW F) (p : ℕ) :
    divisorWeilSpan hF hB hD hT A hW p ≤ F p :=
  iInf₂_le F hFc

/-- `divisorWeilSpan` contains the generators and is cup-closed. -/
theorem isDivisorWeilClosed_divisorWeilSpan :
    IsDivisorWeilClosed hF hB hD hT A hW (divisorWeilSpan hF hB hD hT A hW) where
  unit_mem := by
    rw [divisorWeilSpan, Submodule.mem_iInf]
    intro F
    rw [Submodule.mem_iInf]
    exact fun hFc => hFc.unit_mem
  hdg_one_le := le_iInf₂ fun _ hFc => hFc.hdg_one_le
  weil_le := le_iInf₂ fun _ hFc => hFc.weil_le
  cup_mem h a b ha hb := by
    rw [divisorWeilSpan, Submodule.mem_iInf] at ha hb ⊢
    intro F
    rw [Submodule.mem_iInf]
    exact fun hFc => hFc.cup_mem h a b ((Submodule.mem_iInf _).mp (ha F) hFc)
      ((Submodule.mem_iInf _).mp (hb F) hFc)

/-- The unit is in `divisorWeilSpan` in degree `0`. -/
theorem unitClass_mem_divisorWeilSpan :
    (show HQ X (2 * 0) from unitClass X) ∈ divisorWeilSpan hF hB hD hT A hW 0 :=
  (isDivisorWeilClosed_divisorWeilSpan hF hB hD hT A hW).unit_mem

/-- The divisor Hodge classes `Hdg¹(X; ℚ)` are in `divisorWeilSpan` in degree `1`. -/
theorem hdg_one_le_divisorWeilSpan : Hdg^1(X; ℚ) ≤ divisorWeilSpan hF hB hD hT A hW 1 :=
  (isDivisorWeilClosed_divisorWeilSpan hF hB hD hT A hW).hdg_one_le

/-- The rational Weil classes are in `divisorWeilSpan` in degree `k`. -/
theorem weilClassOf_le_divisorWeilSpan :
    letI := hT.finite
    weilClassOf hF hB hD hT A hW ≤ divisorWeilSpan hF hB hD hT A hW (Module.finrank ℂ
      ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0))) :=
  (isDivisorWeilClosed_divisorWeilSpan hF hB hD hT A hW).weil_le

/-- `divisorWeilSpan` is closed under cup product. -/
theorem cup_mem_divisorWeilSpan {p q : ℕ} (h : 2 * p + 2 * q = 2 * (p + q)) (a : HQ X (2 * p))
    (b : HQ X (2 * q)) (ha : a ∈ divisorWeilSpan hF hB hD hT A hW p)
    (hb : b ∈ divisorWeilSpan hF hB hD hT A hW q) :
    μ.cup h a b ∈ divisorWeilSpan hF hB hD hT A hW (p + q) :=
  (isDivisorWeilClosed_divisorWeilSpan hF hB hD hT A hW).cup_mem h a b ha hb

end DivisorWeilSpan

/-- **The Hodge ring of `X` is generated by divisors and the Weil classes of `A`**: for every `p`,
`Hdg^p(X; ℚ)` lies in `divisorWeilSpan A hW p`, the subring generated by `1`, `Hdg¹(X; ℚ)` and the
rational Weil classes `weilClassOf A hW`.

Source: Moonen–Zarhin, *Hodge classes on abelian varieties of low dimension*, Math. Ann. 315 (1999) (the dimension-4 case); van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, in *Algebraic Cycles and Hodge Theory* (Torino 1993), LNM 1594 (the Weil-type case with Hodge group `SU_H`). Paper level only.

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism of `H¹` that preserves the Hodge
pieces. Such endomorphisms are exactly `End⁰(X)` acting on `H¹` (Birkenhake–Lange, *Complex Abelian
Varieties*, 2nd ed., Grundlehren 302, Ch. 1); that identification is not formalized.

**Consistency.**
(i) Where it is known to hold: a Weil-type abelian variety whose Hodge group is `SU_H` (van
Geemen), which for `dim X = 6` with the `M` datum is F-1575's case `m = 1`; and a generic Weil-type
abelian fourfold (Moonen–Zarhin).
(ii) Where it **fails**: on `A^m` for `m ≥ 2` with the diagonal action, **when the Weil class of `A`
is exceptional** (not in the divisor subring of `A`; for example when the Hodge group of `A` is
`SU_H`, as for the sixfolds of `M`). Then F-1575's generators include
the pullbacks `det(W ⊗ a)` of the Weil classes of `A` along `K`-linear maps `a : A^m → A`. They lie
in `H⁶` and are not products of divisors, while the Weil classes of `A^m` lie in `H^(6m)`
(`2k = dim A^m = 6m`, `two_mul_finrank_vs_inf_h10_eq`). So in degree `6` this span holds only
products of divisor classes, and the hypothesis is false there: in that case the connector applies
to `A`, not to `A^m`. Without the exceptional-class condition the failure need not occur: for `E` an
elliptic curve with CM and `A = E⁶` with a Weil-type action, every power has a Hodge ring
generated by divisors (van Geemen, LNM 1594, Theorem 4.3, as cited by the statement review), so the
hypothesis holds on all `A^m`. (Check of "not products of divisors": restricting along the inclusion `A → A^m` of the
first factor sends divisor products to divisor products and the pullback of a Weil class `w` along
the first projection back to `w`, which is not in the divisor subring of `A` when its Hodge group is
`SU_H`.)
(iii) It is not vacuous: by (ii) it is a real restriction on `X`, false for some abelian varieties
with a Weil-type action. -/
@[hodge_hypothesis]
structure HodgeRingGeneratedByDivisorsAndWeil (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) : Prop where
  generated : ∀ p : ℕ, Hdg^p(X; ℚ) ≤ divisorWeilSpan hF hB hD hT A hW p

/-- **The connector: algebraic Weil classes plus generation give the Hodge conjecture for `X`.**
For an abelian `X` with a Weil-type action `A` on `H¹(X(ℂ); ℚ)`: if every rational Weil class is
algebraic (`WeilClassesAlgebraic`, F-1569's claim for `X`) and the Hodge ring is generated by
divisors and the Weil classes (`HodgeRingGeneratedByDivisorsAndWeil`), then
`Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p` for every `p`. The algebraic classes form a family that
contains the generators (`[X] = 1`, so the unit is algebraic; `Hdg¹` by Lefschetz (1,1); the Weil
classes by `WeilClassesAlgebraic`) and is cup-closed (C9), so `divisorWeilSpan_le` puts the
generated subring inside it.

This is the formal form of: F-1569 for `X`, plus generation, gives HC for `X`.
F-1569's claim is this statement when `(X, A)` is a member of `M = (3, ℚ(√−3), [−2])` with
its `ℚ(√−3)`-action; for any other `X` or action it is not F-1569.

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism of `H¹` that preserves the Hodge
pieces. Such endomorphisms are exactly `End⁰(X)` acting on `H¹`; that identification is not
formalized.

Source: Fulton, *Intersection Theory*, 2nd ed., Ergeb. Math. Grenzgeb. (3) 2, Ch. 19, Corollary 19.2 (through `CycleClassMultiplicative`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through `LefschetzOneOneHyp`); the reduction itself is proved here.

| hypothesis | roadmap / role |
| --- | --- |
| `hF : FiniteBetti X` | C1, fixes the package `S` |
| `hB : BettiDeRhamIso X` | C2, fixes the package `S` |
| `hD : HodgeDecomposition X` | C4, fixes the package `S` |
| `hT : TorusCohomology μ` | C7, fixes the package `S` and `weilClassOf` |
| `A : WeilAction S.weight1 d`, `hW : A.IsWeilType` | the Weil-type action (data) |
| `hWA : WeilClassesAlgebraic A hW` | F-1569 for `X`: **stated, not proved** |
| `hGen : HodgeRingGeneratedByDivisorsAndWeil A hW` | generation: **not proved**; false on `A^m`, `m ≥ 2`, when the Weil class of `A` is exceptional (e.g. Hodge group `SU_H`) |
| `hM : CycleClassMultiplicative μ` | C9, cup-closure of algebraic classes |
| `h11 : LefschetzOneOneHyp` | Lefschetz (1,1), `Hdg¹ ≤ span 1` |

O5 (`CupFiltered`) is not bound: the connector does not use that the Weil classes are Hodge classes
(`weilClassOf_le_hdg`). Neither is `d > 0`.

Relation to the goal: HC no distance. AV milestone no distance; the connector reduces HC for `X` to
F-1569 plus generation, both outside Lean. -/
@[hodge_milestone] theorem hdg_le_span_of_weilClassesAlgebraic (hF : FiniteBetti X)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) (hWA : WeilClassesAlgebraic hF hB hD hT A hW)
    (hGen : HodgeRingGeneratedByDivisorsAndWeil hF hB hD hT A hW)
    (hM : CycleClassMultiplicative μ) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := fun p =>
  (hGen.generated p).trans <| divisorWeilSpan_le hF hB hD hT A hW
    (F := fun p => algebraicCycleClassSpan X p)
    { unit_mem := unitClass_mem_algebraicCycleClassSpan
      hdg_one_le := h11.holds X
      weil_le := hWA
      cup_mem := fun h a b ha hb => hM.mem h a b ha hb } p

/-- The Blocks-side statement for this `X` follows too: the transfer converse
`hodgeConjectureFor_of_hdg_le_span` applied to the connector's conclusion. -/
example (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) (hWA : WeilClassesAlgebraic hF hB hD hT A hW)
    (hGen : HodgeRingGeneratedByDivisorsAndWeil hF hB hD hT A hW)
    (hM : CycleClassMultiplicative μ) (h11 : LefschetzOneOneHyp) :
    letI := hT.finite
    HodgeBlocks.HodgeConjectureFor (abelianVarietyCohomologyOf hF hB hD hT)
      (fun {m} => isAlgebraicOf μ (m := m)) :=
  hodgeConjectureFor_of_hdg_le_span hF hB hD hT
    (hdg_le_span_of_weilClassesAlgebraic hF hB hD hT A hW hWA hGen hM h11)

end WeilClasses

end HodgeLean.RealDefs
