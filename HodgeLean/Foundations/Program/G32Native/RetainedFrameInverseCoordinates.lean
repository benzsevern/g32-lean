import HodgeLean.Foundations.BundleThom.NormalAtlasConstructionHelpers
import HodgeLean.Foundations.BundleThom.ConormalFrameRestrictionHelpers

/-! # Inverse coordinates of the original normal trivialization -/

noncomputable section
set_option maxHeartbeats 100000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Bundle
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

private local instance normalTotalTop {Y : Over (Spec ↧ℂ)} {X : Scheme}
    (j : Y.left ⟶ X) (k : ℕ) :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- The inverse chart uses the dual of the specified original frame. -/
theorem retained_normal_frame_inverse
    {Y : Over (Spec ↧ℂ)} {X : Scheme} (j : Y.left ⟶ X) (k : ℕ)
    (U : Y.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (x : ComplexPoint Y) (hx : x ∈ Point.overOpen U) (w : Fin k → ℂ) :
    (i1_normalFrameTrivialization j k U E).toOpenPartialHomeomorph.symm (x, w) =
      (⟨x, (i1_conormalFrameBasis j k U E x hx).dualBasis.equivFun.symm w⟩ :
        TotalSpace (Fin k → ℂ) (i1_normalFibre j)) := by
  classical
  let e := i1_normalFrameTrivialization j k U E
  letI : e.IsLinear ℂ := i1_normalFrameTrivialization_isLinear j k U E
  have hb : x ∈ e.baseSet := hx
  have he : e.linearEquivAt ℂ x hb =
      (i1_conormalFrameBasis j k U E x hx).dualBasis.equivFun := by
    apply LinearEquiv.ext
    intro v
    change (if h : x ∈ Point.overOpen U then
      (i1_normalFrameHomeomorph j k U E ⟨⟨x, v⟩, h⟩).2 else 0) = _
    erw [dite_eq_left hx]
    rfl
  change e.toOpenPartialHomeomorph.symm (x, w) = _
  rw [← e.mk_symm hb w, ← e.linearEquivAt_symm_apply (R := ℂ) x hb w, he]

/-- Shrinking the algebraic base open retains the same inverse fibre coordinates. -/
theorem retained_normal_frame_inverse_restriction
    {Y : Over (Spec ↧ℂ)} {X : Scheme} (j : Y.left ⟶ X) (k : ℕ)
    {U V : Y.left.Opens} (hVU : V ≤ U)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k))
    (x : ComplexPoint Y) (hx : x ∈ Point.overOpen V) (w : Fin k → ℂ) :
    (i1_normalFrameTrivialization j k V
      (i1_conormalFrameRestriction j k hVU E)).toOpenPartialHomeomorph.symm (x, w) =
      (i1_normalFrameTrivialization j k U E).toOpenPartialHomeomorph.symm (x, w) := by
  rw [retained_normal_frame_inverse j k V _ x hx,
    retained_normal_frame_inverse j k U E x (hVU hx),
    i1_conormalFrameBasis_restriction]

#print axioms retained_normal_frame_inverse
#print axioms retained_normal_frame_inverse_restriction
end HodgeLean.Foundations.TubularEuler
