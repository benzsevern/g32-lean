import HodgeLean.Foundations.Program.SchoenGenericIdealPullback

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual quasi-compact dominant morphism into a reduced scheme is injective on sections of every affine open. -/
theorem s2_dominant_app_injective {X Y : Scheme.{0}} [IsReduced Y]
    (f : X ⟶ Y) [QuasiCompact f] [IsDominant f] (U : Y.affineOpens) :
    Function.Injective (f.app U).hom := by
  have hk : f.ker = ⊥ := by
    apply Scheme.IdealSheafData.support_eq_top_iff.mp
    apply SetLike.coe_injective
    change (f.ker.support : Set Y) = Set.univ
    rw [Scheme.Hom.support_ker, f.denseRange.closure_range]
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  rw [← Scheme.Hom.ker_apply, hk]
  rfl

end HodgeLean.Foundations.Program
