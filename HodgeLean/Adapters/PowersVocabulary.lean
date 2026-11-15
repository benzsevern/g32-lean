import HodgeLean.Adapters.PowersVocabularyProofs

/-! # The Powers flagship, stage PW-0: vocabulary for `Hg(A) = G_k(A)` and generation without family M (FROZEN SPEC)

Stage PW-0 of formalizing PW v0.3, Theorem 4.2 (`thm:gen`), "Hodge classes on powers of abelian
varieties of Weil type and of type IV with exact endomorphism algebra"
(doi:10.5281/zenodo.23570103). Each theorem is proved by the matching `_aux` theorem in
`PowersVocabularyProofs.lean`. The definitions are in `Foundations/PowersVocabularyDefs.lean`.

It claims, in the exterior-algebra model `⋀ (V ⊗ ℚ^m)` of `H^*(A^m)`:

* `gkLie` at `R = ℚ[J]` is EQW's `weilSU E J`, and `HodgeLieIsGk` at `R = ℚ[J]`, `J² = -3`, is
  equivalent to the hypothesis `hSU` of `exteriorHodgeClasses_eq_generated`;
* Weil type follows from `HodgeLieIsGk`, for every `d > 0` and every subalgebra `R`;
* `cmPowerPullback` and `cmPowerSpan` at `R = ℚ[J]` (with `J² ∈ ℚ`) are `weilPowerPullback` and
  `divisorPulledWeilSpan`;
* the span `cmPowerSpan` consists of rational Hodge classes, unconditionally (no Hodge-group
  hypothesis), and the rational Weil classes are in the kernel of the induced grading;
* F-1575's powers results (`F1575PowersFix` S3, S4) **without the family-M hypothesis `hM`**:
  for any weight-one rational Hodge structure with a Weil action of `ℚ(√-3)` (`J² = -3`) of Weil
  type, any nondegenerate `J`-skew form `E`, in any dimension, as an implication from `hSU`; the
  same in the vocabulary of Theorem 4.2, as an implication from `HodgeLieIsGk` alone (Weil type
  derived); and the instance on `H¹` of an abelian variety, with no dimension, discriminant or
  positivity hypothesis;
* falsification: `HodgeLieIsGk` fails on the CM structure `hsuCMHodge`.

It does not claim: anything for a CM field `L ≠ k` (`e > 1`) or for `k ≠ ℚ(√-3)` in the
generation statements (`complexSU` and the transport are defined only for `J² = -3`); the
identification of the model with the cohomology `H^*(A^m)` of an actual power, or pullback along
an actual morphism `f_a`; that the degree-two generators are divisor classes (Lefschetz (1,1) is
neither assumed nor used); the algebraic-group form of `Hg(A) = G_k(A)` (only its Lie-algebra form
is stated); any algebraicity. HC no distance; AV milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory AlgebraicGeometry ComplexPoint
open scoped TensorProduct
namespace HodgeLean.Adapters
open RealDefs Foundations Foundations.WeilPower Foundations.Symplectic InvariantsExterior

section Algebra

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- **`G_k` at `L = k`.** For `R = ℚ[J]`, commuting with `R` is commuting with `J`, so `gkLie` is
EQW's `weilSU E J`: at `e = 1`, `G_k(A) = SU(V, H)`.
Source: PW v0.3, proof of Theorem 3.1, first paragraph (`L = k`, `G_k(A) = SU(V,H)`); `weilSU`
(`Foundations/EQWCoreDefs.lean`). -/
theorem spec_pw0_gkLie_adjoin_eq (E : LinearMap.BilinForm ℚ V) (J : Module.End ℚ V) :
    gkLie E (Algebra.adjoin ℚ {J}) J = weilSU E J :=
  spec_pw0_gkLie_adjoin_eq_aux E J

example (E : LinearMap.BilinForm ℚ V) (J : Module.End ℚ V) :
    gkLie E (Algebra.adjoin ℚ {J}) J = weilSU E J :=
  spec_pw0_gkLie_adjoin_eq E J

/-- **`cmPowerPullback` at `R = ℚ[J]`** is the pullback `weilPowerPullback J r s` of F-1575, for
the coefficients `a_i = r_i + s_i J`. No quadratic relation is needed.
Source: PW v0.3, Theorem 4.2 (the maps `f_a`); `weilPowerPullback`
(`Foundations/WeilPowerSpan.lean`). -/
theorem spec_pw0_cmPowerPullback_adjoin (J : Module.End ℚ V) {m : ℕ} (r s : Fin m → ℚ) :
    cmPowerPullback (Algebra.adjoin ℚ {J})
        (fun i => algebraMap ℚ (Algebra.adjoin ℚ {J}) (r i) +
          s i • ⟨J, Algebra.self_mem_adjoin_singleton ℚ J⟩) =
      weilPowerPullback J r s :=
  spec_pw0_cmPowerPullback_adjoin_aux J r s

example (J : Module.End ℚ V) (r s : Fin 2 → ℚ) :
    cmPowerPullback (Algebra.adjoin ℚ {J})
        (fun i => algebraMap ℚ (Algebra.adjoin ℚ {J}) (r i) +
          s i • ⟨J, Algebra.self_mem_adjoin_singleton ℚ J⟩) =
      weilPowerPullback J r s :=
  spec_pw0_cmPowerPullback_adjoin J r s

/-- **`cmPowerSpan` at `R = ℚ[J]`** is `divisorPulledWeilSpan`, when `J² = -d` for some rational
`d`: then every element of `ℚ[J]` is `r + s J`, so the two closure conditions agree.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Conclusion"; `divisorPulledWeilSpan`
(`Foundations/WeilPowerSpan.lean`). -/
theorem spec_pw0_cmPowerSpan_adjoin_eq (J : Module.End ℚ V) {d : ℚ}
    (hJ : J.comp J = (-d) • LinearMap.id) {m n : ℕ}
    (D : Submodule ℚ (⋀[ℚ]^2 (V ⊗[ℚ] (Fin m → ℚ)))) (W : Submodule ℚ (⋀[ℚ]^n V)) (k : ℕ) :
    cmPowerSpan (Algebra.adjoin ℚ {J}) D W k = divisorPulledWeilSpan J D W k :=
  spec_pw0_cmPowerSpan_adjoin_eq_aux J hJ D W k

example (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id) {m n : ℕ}
    (D : Submodule ℚ (⋀[ℚ]^2 (V ⊗[ℚ] (Fin m → ℚ)))) (W : Submodule ℚ (⋀[ℚ]^n V)) (k : ℕ) :
    cmPowerSpan (Algebra.adjoin ℚ {J}) D W k = divisorPulledWeilSpan J D W k :=
  spec_pw0_cmPowerSpan_adjoin_eq J hJ D W k

variable [FiniteDimensional ℚ V]

/-- **(P3) at `L = k = ℚ(√-3)` is `hSU`.** By `spec_pw0_gkLie_adjoin_eq` and
`spec_eqw_complexSpan_weilSU_eq_complexSU`, `HodgeLieIsGk` at `R = ℚ[J]` is the equality of
`F1575MemberHodgeGroupIsSU`'s shape.
Source: PW v0.3, proof of Theorem 3.1, first paragraph (`G_k(A) = SU(V,H)` at `e = 1`);
`spec_eqw_complexSpan_weilSU_eq_complexSU` (`Foundations/EQWCore.lean`). -/
theorem spec_pw0_hodgeLieIsGk_adjoin_iff (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
    (hH : DirectSum.IsInternal H) (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hAlt : E.IsAlt) (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id)
    (hskew : ∀ x y, E (J x) y = -E x (J y)) :
    HodgeLieIsGk H hH E (Algebra.adjoin ℚ {J}) J ↔
      complexSpan (hodgeLieAlgebra H hH).toSubmodule =
        (complexSU E hE J hJ hskew).toSubmodule :=
  spec_pw0_hodgeLieIsGk_adjoin_iff_aux H hH E hE hAlt J hJ hskew

example (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
    (hH : DirectSum.IsInternal H) (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hAlt : E.IsAlt) (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id)
    (hskew : ∀ x y, E (J x) y = -E x (J y)) :
    HodgeLieIsGk H hH E (Algebra.adjoin ℚ {J}) J ↔
      complexSpan (hodgeLieAlgebra H hH).toSubmodule =
        (complexSU E hE J hJ hskew).toSubmodule :=
  spec_pw0_hodgeLieIsGk_adjoin_iff H hH E hE hAlt J hJ hskew

/-- **The span consists of rational Hodge classes, unconditionally.** If every element of `R`
preserves the Hodge pieces and every element of `W` is killed by the induced grading operator
(is a Hodge class), then `cmPowerSpan R` with degree-two generators the rational degree-two Hodge
classes of the power lies in the rational Hodge classes of the power. No Hodge-group hypothesis.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Conclusion" ("It consists of Hodge classes");
`rationalExteriorHodge` (`Foundations/WeilPowerClasses.lean`). -/
theorem spec_pw0_cmPowerSpan_le_rationalExteriorHodge
    (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
    (R : Subalgebra ℚ (Module.End ℚ V))
    (hR : ∀ r ∈ R, ∀ pq, ∀ x ∈ H pq, (r : Module.End ℚ V).baseChange ℂ x ∈ H pq)
    {n : ℕ} (W : Submodule ℚ (⋀[ℚ]^n V))
    (hW : ∀ w ∈ W, exteriorDer n (gradingOperator H hH) (exteriorComplexify n w) = 0)
    (m k : ℕ) :
    cmPowerSpan R (rationalExteriorHodge H hH m 2) W k ≤ rationalExteriorHodge H hH m k :=
  spec_pw0_cmPowerSpan_le_rationalExteriorHodge_aux H hH R hR W hW m k

example (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
    (R : Subalgebra ℚ (Module.End ℚ V))
    (hR : ∀ r ∈ R, ∀ pq, ∀ x ∈ H pq, (r : Module.End ℚ V).baseChange ℂ x ∈ H pq)
    {n : ℕ} (W : Submodule ℚ (⋀[ℚ]^n V))
    (hW : ∀ w ∈ W, exteriorDer n (gradingOperator H hH) (exteriorComplexify n w) = 0) :
    cmPowerSpan R (rationalExteriorHodge H hH 3 2) W 4 ≤ rationalExteriorHodge H hH 3 4 :=
  spec_pw0_cmPowerSpan_le_rationalExteriorHodge H hH R hR W hW 3 4

end Algebra

section Weil

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {M : HodgeBlocks.QHodgeStructure 1 V}

/-- **Weil type follows from (P3).** The grading operator `C` lies in the complexified Hodge Lie
algebra, hence in the complexified `gkLie`, so `tr C = 0` and `tr (J_ℂ C) = 0`. As `C` is `i` on
`H^{1,0}` and `-i` on `H^{0,1}`, and `J_ℂ` is `±i√d` on `V₊`, `V₋`, these say
`dim (V₊ ∩ H^{1,0}) = dim (V₊ ∩ H^{0,1})`, which is Weil type. Any `d > 0`, any `E`, any `R`.
Source: PW v0.3, Subsection 2.2, last paragraph (`W_k(A)` is Hodge iff `p_σ = q_σ`, and then
`Hg(A) ⊆ SL_k(V)`) and Subsection 2.3 (`G_k(A) ⊆ SL_k(V)`); `spec_eqw_mem_complexSpan_weilSU_iff`,
`gradingOperator_mem_span_hodgeLieAlgebra`. -/
theorem isWeilType_of_hodgeLieIsGk {d : ℚ} (hd : 0 < d) (A : HodgeBlocks.WeilAction M d)
    (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (E : LinearMap.BilinForm ℚ V)
    (R : Subalgebra ℚ (Module.End ℚ V)) (hGk : HodgeLieIsGk M.H M.isInternal E R A.J) :
    A.IsWeilType :=
  isWeilType_of_hodgeLieIsGk_aux hd A hTop E R hGk

example (A : HodgeBlocks.WeilAction M 3)
    (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (E : LinearMap.BilinForm ℚ V)
    (hGk : HodgeLieIsGk M.H M.isInternal E (Algebra.adjoin ℚ {A.J}) A.J) :
    A.IsWeilType :=
  isWeilType_of_hodgeLieIsGk (by norm_num) A hTop E _ hGk

/-- **Rational Weil classes are Hodge, in grading form**: every element of `A.weilClasses` is
killed by the grading operator induced on `⋀ (ℂ ⊗ V)`. This is the hypothesis `hW` of
`spec_pw0_cmPowerSpan_le_rationalExteriorHodge` for the Weil space.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §6 (Weil
classes are Hodge classes); Blocks `isHodgeClass_of_mem_weilClasses`. -/
theorem spec_pw0_weilClasses_grading {d : ℚ} (A : HodgeBlocks.WeilAction M d)
    (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) :
    ∀ w ∈ A.weilClasses hTop hW,
      exteriorDer _ (gradingOperator M.H M.isInternal) (exteriorComplexify _ w) = 0 :=
  spec_pw0_weilClasses_grading_aux A hTop hW

example (A : HodgeBlocks.WeilAction M 3)
    (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) :
    ∀ w ∈ A.weilClasses hTop hW,
      exteriorDer _ (gradingOperator M.H M.isInternal) (exteriorComplexify _ w) = 0 :=
  spec_pw0_weilClasses_grading A hTop hW

/-- **F1575PowersFix S3 without family M**: for any weight-one rational Hodge structure with a
Weil action of `ℚ(√-3)` of Weil type and any nondegenerate `J`-skew form `E`, in any dimension,
the complex Hodge classes of `⋀^k (V ⊗ ℚ^m)` are exactly the complexified span of `1`, the
rational degree-two Hodge classes and the pullbacks of the rational Weil classes. Implication
from `hSU`.
Source: PW v0.3, Theorem 4.2 at `L = k = ℚ(√-3)`; F-1575 / TR54 §3; van Geemen, *An introduction
to the Hodge conjecture for abelian varieties*, §§5–6; `f1575Power_hodgeClasses_eq_hodgeTwoPulledWeilSpan`
(the case of a member of `M`). -/
theorem spec_pw0_exteriorHodgeClasses_eq_divisorPulledWeilSpan
    (A : HodgeBlocks.WeilAction M 3) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hskew : ∀ x y, E (A.J x) y = -E x (A.J y))
    (hSU : complexSpan (hodgeLieAlgebra M.H M.isInternal).toSubmodule =
      (complexSU E hE A.J A.J_sq hskew).toSubmodule) (m k : ℕ) :
    exteriorHodgeClasses M.H M.isInternal m k =
      ((divisorPulledWeilSpan A.J (rationalExteriorHodge M.H M.isInternal m 2)
        (A.weilClasses hTop hW) k).baseChange ℂ).map (exteriorBaseChange k).toLinearMap :=
  spec_pw0_exteriorHodgeClasses_eq_divisorPulledWeilSpan_aux A hTop hW E hE hskew hSU m k

example (A : HodgeBlocks.WeilAction M 3) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤)
    (hW : A.IsWeilType) (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hskew : ∀ x y, E (A.J x) y = -E x (A.J y))
    (hSU : complexSpan (hodgeLieAlgebra M.H M.isInternal).toSubmodule =
      (complexSU E hE A.J A.J_sq hskew).toSubmodule) :
    exteriorHodgeClasses M.H M.isInternal 2 4 =
      ((divisorPulledWeilSpan A.J (rationalExteriorHodge M.H M.isInternal 2 2)
        (A.weilClasses hTop hW) 4).baseChange ℂ).map (exteriorBaseChange 4).toLinearMap :=
  spec_pw0_exteriorHodgeClasses_eq_divisorPulledWeilSpan A hTop hW E hE hskew hSU 2 4

/-- **F1575PowersFix S4 without family M**: the rational form. The rational Hodge classes of
`⋀^k (V ⊗ ℚ^m)` are exactly the span. Implication from `hSU`.
Source: as `spec_pw0_exteriorHodgeClasses_eq_divisorPulledWeilSpan`;
`f1575Power_rationalExteriorHodge_eq_hodgeTwoPulledWeilSpan` (the case of a member of `M`). -/
theorem spec_pw0_rationalExteriorHodge_eq_divisorPulledWeilSpan
    (A : HodgeBlocks.WeilAction M 3) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hskew : ∀ x y, E (A.J x) y = -E x (A.J y))
    (hSU : complexSpan (hodgeLieAlgebra M.H M.isInternal).toSubmodule =
      (complexSU E hE A.J A.J_sq hskew).toSubmodule) (m k : ℕ) :
    rationalExteriorHodge M.H M.isInternal m k =
      divisorPulledWeilSpan A.J (rationalExteriorHodge M.H M.isInternal m 2)
        (A.weilClasses hTop hW) k :=
  spec_pw0_rationalExteriorHodge_eq_divisorPulledWeilSpan_aux A hTop hW E hE hskew hSU m k

example (A : HodgeBlocks.WeilAction M 3) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤)
    (hW : A.IsWeilType) (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hskew : ∀ x y, E (A.J x) y = -E x (A.J y))
    (hSU : complexSpan (hodgeLieAlgebra M.H M.isInternal).toSubmodule =
      (complexSU E hE A.J A.J_sq hskew).toSubmodule) :
    rationalExteriorHodge M.H M.isInternal 3 6 =
      divisorPulledWeilSpan A.J (rationalExteriorHodge M.H M.isInternal 3 2)
        (A.weilClasses hTop hW) 6 :=
  spec_pw0_rationalExteriorHodge_eq_divisorPulledWeilSpan A hTop hW E hE hskew hSU 3 6

/-- **Theorem 4.2 (C1) at `L = k = ℚ(√-3)`, in the model, from (P3) alone.** Under
`HodgeLieIsGk` for `R = ℚ[J]`, the rational Hodge classes of `⋀^k (V ⊗ ℚ^m)` are exactly
`cmPowerSpan`, generated by `1`, the rational degree-two Hodge classes and the pullbacks of the
rational Weil classes along every `cmPowerPullback`. Weil type is not a binder: it is derived by
`isWeilType_of_hodgeLieIsGk`.
Source: PW v0.3, Theorem 4.2, first sentence, at `e = 1`, `k = ℚ(√-3)`, in the exterior-algebra
model; `spec_pw0_rationalExteriorHodge_eq_divisorPulledWeilSpan`,
`spec_pw0_hodgeLieIsGk_adjoin_iff`, `spec_pw0_cmPowerSpan_adjoin_eq`. -/
theorem spec_pw0_rationalExteriorHodge_eq_cmPowerSpan
    (A : HodgeBlocks.WeilAction M 3) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hskew : ∀ x y, E (A.J x) y = -E x (A.J y))
    (hGk : HodgeLieIsGk M.H M.isInternal E (Algebra.adjoin ℚ {A.J}) A.J) (m k : ℕ) :
    rationalExteriorHodge M.H M.isInternal m k =
      cmPowerSpan (Algebra.adjoin ℚ {A.J}) (rationalExteriorHodge M.H M.isInternal m 2)
        (A.weilClasses hTop
          (isWeilType_of_hodgeLieIsGk (by norm_num) A hTop E _ hGk)) k :=
  spec_pw0_rationalExteriorHodge_eq_cmPowerSpan_aux A hTop E hE hAlt hskew hGk m k

example (A : HodgeBlocks.WeilAction M 3) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hskew : ∀ x y, E (A.J x) y = -E x (A.J y))
    (hGk : HodgeLieIsGk M.H M.isInternal E (Algebra.adjoin ℚ {A.J}) A.J) :
    rationalExteriorHodge M.H M.isInternal 2 2 =
      cmPowerSpan (Algebra.adjoin ℚ {A.J}) (rationalExteriorHodge M.H M.isInternal 2 2)
        (A.weilClasses hTop
          (isWeilType_of_hodgeLieIsGk (by norm_num) A hTop E _ hGk)) 2 :=
  spec_pw0_rationalExteriorHodge_eq_cmPowerSpan A hTop E hE hAlt hskew hGk 2 2

end Weil

section Geometric

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  {μ : CupProduct X} [GrpObj X]

/-- **The abelian-variety instance, with no family-M hypothesis.** For `H¹` of an abelian
variety (through the package `hF hB hD hT`), any Weil action of `ℚ(√-3)` of Weil type, and any
class `η` whose 2-vector is nondegenerate and Rosati-compatible with `J`: no dimension, no
discriminant and no positivity hypothesis. Implication from `hSU` in
`F1575MemberHodgeGroupIsSU`'s shape. At `m = 1` this is still a statement about the model
`⋀ (H¹ ⊗ ℚ¹)`; the comparison with `H^*(X)` is `f1575PowerOne_map_eq_divisorWeilSpan`'s.
Source: `f1575Power_rationalExteriorHodge_eq_hodgeTwoPulledWeilSpan` with `hM` removed;
`polarizationForm`, `polarizationForm_skew` (`RealDefs/F1569.lean`). -/
theorem spec_pw0_abelian_rationalExteriorHodge_eq (hF : FiniteBetti X)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    (hW : letI := hT.finite; A.IsWeilType) {η : HQ X 2}
    (hω : IsNondegenerate (polarizationVec hT η))
    (hR : letI := hT.finite; IsRosatiSkew (polarizationVec hT η) A.J)
    (hSU : letI := hT.finite
      complexSpan (hodgeLieAlgebra (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
          (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal).toSubmodule =
        (complexSU (polarizationForm hT hω) (nondegenerate_polarizationForm hT hω) A.J A.J_sq
          (polarizationForm_skew hT hω hR)).toSubmodule)
    (m k : ℕ) :
    letI := hT.finite
    let S := abelianVarietyCohomologyOf hF hB hD hT
    rationalExteriorHodge S.weight1.H S.weight1.isInternal m k =
      divisorPulledWeilSpan A.J (rationalExteriorHodge S.weight1.H S.weight1.isInternal m 2)
        (A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hW) k :=
  spec_pw0_abelian_rationalExteriorHodge_eq_aux hF hB hD hT A hW hω hR hSU m k

example (hF : FiniteBetti X)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    {η : HQ X 2} (hM : IsMemberOfM hF hB hD hT A η)
    (hSU : F1575MemberHodgeGroupIsSU hF hB hD hT A hM) (m k : ℕ) :
    letI := hT.finite
    let S := abelianVarietyCohomologyOf hF hB hD hT
    rationalExteriorHodge S.weight1.H S.weight1.isInternal m k =
      divisorPulledWeilSpan A.J (rationalExteriorHodge S.weight1.H S.weight1.isInternal m 2)
        (A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType) k :=
  spec_pw0_abelian_rationalExteriorHodge_eq hF hB hD hT A hM.isWeilType hM.nondegenerate
    hM.rosati hSU m k

end Geometric

/-- **Falsification: (P3) fails on a CM point.** For the CM structure `hsuCMHodge` on `ℚ¹²`,
which is of Weil type and polarized, `HodgeLieIsGk` at `R = ℚ[J]` fails: its Hodge Lie algebra is
a line, against the 35-dimensional `𝔰𝔩₆`.
Source: `spec_hsuCMHodge_hSU_fails` (`Foundations/HSUCandidateHodge.lean`) with
`spec_pw0_hodgeLieIsGk_adjoin_iff`; PW v0.3, Remark 4.3 (without (P3) the conclusion can fail). -/
theorem spec_pw0_not_hodgeLieIsGk_hsuCMHodge :
    ¬ HodgeLieIsGk hsuCMHodge spec_hsuCMHodge_isInternal hsuE (Algebra.adjoin ℚ {hsuJ}) hsuJ :=
  spec_pw0_not_hodgeLieIsGk_hsuCMHodge_aux

example :
    ¬ HodgeLieIsGk hsuCMHodge spec_hsuCMHodge_isInternal hsuE (Algebra.adjoin ℚ {hsuJ}) hsuJ :=
  spec_pw0_not_hodgeLieIsGk_hsuCMHodge

end HodgeLean.Adapters
