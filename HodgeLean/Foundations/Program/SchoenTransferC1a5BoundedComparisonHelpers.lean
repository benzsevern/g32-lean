import HodgeLean.Foundations.Program.SchoenTransferC1a5SkeletonHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5DimensionHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5TopHelpers

/-! Joint dimension induction for boundary and skeletal comparison.
Each boundary used in the induction has strictly smaller dimension.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- Integral unit comparison by dimension induction, using lower-dimensional boundaries only.
Source: Hatcher §2.1, Theorem 2.27, skeletal comparison with characteristic-cell excision. -/
lemma c1a5_bounded_unit_comparison (d : ℕ) (K : SSet.{0}) [K.Finite] [K.HasDimensionLT d] :
    QuasiIso (c1a5Unit K) := by
  induction d generalizing K with
  | zero =>
    have heq : (⊥ : K.Subcomplex) = ⊤ :=
      (K.skeleton_zero).symm.trans (c1a5_skeleton_eq_top K 0)
    let e : (⊥ : K.Subcomplex).toSSet ≅ K :=
      SSet.Subcomplex.eqToIso heq ≪≫ SSet.Subcomplex.topIso K
    have h0 := c1a5_empty_comparison (⊥ : K.Subcomplex).toSSet SSet.Subcomplex.isInitialBot
    have hc : QuasiIso (c1a5Chains.map e.hom ≫ c1a5Unit K) := by
      rw [c1a5Unit_naturality]
      have := h0
      infer_instance
    have := hc
    exact quasiIso_of_comp_left (c1a5Chains.map e.hom) _
  | succ d ih =>
    have := c1a5_skeleton_dimension K d
    have hp := ih (K.skeleton d : SSet)
    have hb := ih (SSet.boundary.{0} d : SSet)
    have hs : QuasiIso (c1a5Unit (Δ[d] : SSet.{0})) := by
      have hC : QuasiIso (c1a5Chains.map (c1a5Augment d)) := c1a5_simplicial_augmentation d
      have hS : QuasiIso (c1a5SingularChains.map (c1a5Augment d)) := c1a5_singular_augmentation d
      have hP : QuasiIso (c1a5Unit (Δ[0] : SSet.{0})) := c1a5_point_comparison
      have hcomp : QuasiIso (c1a5Unit (Δ[d] : SSet.{0}) ≫
          c1a5SingularChains.map (c1a5Augment d)) := by
        rw [← c1a5Unit_naturality]
        infer_instance
      have := hcomp
      exact quasiIso_of_comp_right _ (c1a5SingularChains.map (c1a5Augment d))
    have hk := c1a5_skeletal_attachment_comparison K d hp hs hb
    let e : (K.skeleton (d + 1) : SSet) ≅ K :=
      SSet.Subcomplex.eqToIso (c1a5_skeleton_eq_top K (d + 1)) ≪≫ SSet.Subcomplex.topIso K
    have hc : QuasiIso (c1a5Chains.map e.hom ≫ c1a5Unit K) := by
      rw [c1a5Unit_naturality]
      have := hk
      infer_instance
    have := hc
    exact quasiIso_of_comp_left (c1a5Chains.map e.hom) _

end HodgeLean.Foundations.Program
