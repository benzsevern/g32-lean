import HodgeLean.Foundations.Program.G32Native.CoefficientProductLocalDetection
import HodgeLean.Foundations.BundleThom.ImmersionDefs

/-! # Normal coclass detection and coordinate invariance in every rank -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.BundleThom

/-- Open local base restrictions detect the degree-zero normal coclass. -/
theorem zeroRankProductCoclass_ext_of_locally_eq {B : Type} [TopologicalSpace B]
    (u v : RelativeCohomology ℚ (i1_productNormalPair B 0) 0)
    (hlocal : ∀ b : B, ∃ U : Opens B, b ∈ U ∧
      relativeCohomologyMap ℚ 0
        (i1_productBaseMap 0 (Subtype.val : U → B) continuous_subtype_val) u =
      relativeCohomologyMap ℚ 0
        (i1_productBaseMap 0 (Subtype.val : U → B) continuous_subtype_val) v) : u = v := by
  classical
  choose U hb he using hlocal
  have hP : IsEmpty (i1_productNormalPair B 0).snd :=
    ⟨fun z => z.2 (Subsingleton.elim z.1.2 0)⟩
  apply i1_relativeCohomologyZero_ext_of_cover hP
    (fun b => i1_productNormalPair (U b) 0)
    (fun b => i1_productBaseMap 0 (Subtype.val : U b → B) continuous_subtype_val) _ u v he
  intro x
  exact ⟨x.1, (⟨x.1, hb x.1⟩, x.2), rfl⟩

/-- Local base normalization detects the Thom coclass, including rank zero. -/
theorem productThomCoclass_ext_of_locally_eq_allRanks {B : Type} [TopologicalSpace B]
    (k : ℕ) (u v : RelativeCohomology ℚ (i1_productNormalPair B k) (2 * k))
    (hlocal : ∀ b : B, ∃ U : Opens B, b ∈ U ∧
      relativeCohomologyMap ℚ (2 * k)
        (i1_productBaseMap k (Subtype.val : U → B) continuous_subtype_val) u =
      relativeCohomologyMap ℚ (2 * k)
        (i1_productBaseMap k (Subtype.val : U → B) continuous_subtype_val) v) : u = v := by
  by_cases hk : k = 0
  · subst k
    exact zeroRankProductCoclass_ext_of_locally_eq u v hlocal
  · exact productThomCoclass_ext_of_locally_eq k (Nat.pos_of_ne_zero hk) u v hlocal

/-- Every continuous invertible complex matrix family preserves normal coclasses in every rank. -/
theorem productMatrixNormalMap_thomDegree_pullback_allRanks {B : Type} [TopologicalSpace B]
    (k : ℕ) (A : B → Matrix (Fin k) (Fin k) ℂ) (hA : Continuous A)
    (hd : ∀ b, (A b).det ≠ 0)
    (u : RelativeCohomology ℚ (puncturedPair ℂ k) (2 * k)) :
    relativeCohomologyMap ℚ (2 * k) (i1_productMatrixNormalMap k A hA hd) u =
      relativeCohomologyMap ℚ (2 * k) (i1_productNormalProjection B k) u := by
  by_cases hk : k = 0
  · subst k
    have hm : i1_productMatrixNormalMap 0 A hA hd = i1_productNormalProjection B 0 := by
      apply MorphismProperty.Arrow.Hom.ext
      · apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        exact Subtype.ext (Subsingleton.elim _ _)
      · apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        apply funext
        intro i
        exact Fin.elim0 i
    rw [hm]
  · exact i1_productMatrixNormalMap_thomDegree_pullback k (Nat.pos_of_ne_zero hk) A hA hd u

end HodgeLean.Foundations.BundleThom
