import HodgeLean.Foundations.Program.G32Native.PairedConormalFreeTargetRank
import HodgeLean.Foundations.Program.G32Native.PairedConormalFibreRankObstruction
import HodgeLean.Foundations.Program.G32Native.PairedConormalModelLocallyFree

/-! # Pointwise nonvanishing of the actual smooth model relation -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native

/-- A unit-plus-rank-k presentation of a supplied smooth conormal model has a
nonzero pulled relation at every actual complex point of the model scheme. -/
theorem conormal_smooth_model_relation_pullback_ne_zero
    (Q W Y : Over (Spec ↧ℂ)) (k : ℕ)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (e : Q.left ≅ Y.left) (M I : Y.left.Modules)
    (E : s2c_conormal ι.left ≅ (Scheme.Modules.pullback e.hom).obj M)
    (a : I ⟶ SheafOfModules.unit Y.left.ringCatSheaf ⊞
      SheafOfModules.free (R := Y.left.ringCatSheaf) (Fin k))
    (eM : cokernel a ≅ M) (x : ComplexPoint Y) :
    (Scheme.Modules.pullback x.left).map a ≠ 0 := by
  apply conormal_relation_pullback_ne_zero_of_fibre_rank
  have hM := (paired_module_fibre_rank_of_fixedFrames M k
    (paired_smooth_conormal_model_frames Q W k k ι Y.left e M E) x).2
  have he := ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    ((Scheme.Modules.pullback x.left).mapIso eM)).toLinearEquiv.finrank_eq
  rw [he, hM, conormal_unit_free_target_fibre_finrank]
  omega

end HodgeLean.Foundations.Program.G32Native
