import HodgeLean.Foundations.Mathlib.GenericFlatSmooth
import Mathlib.Data.Complex.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! Generic smoothness supplied by an actual nonempty etale support restriction. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
namespace HodgeLean.Foundations.Program

/-- A nonempty etale support restriction forces dominance of the ambient
map and supplies its dense smooth base open in characteristic zero. -/
theorem s4_q3_generic_smooth_of_etale_support
    (X T : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral T.left] [LocallyOfFiniteType T.hom]
    (h : X ⟶ T) [LocallyOfFinitePresentation h.left] [QuasiCompact h.left]
    (C : Scheme.{0}) [Nonempty C] (i : C ⟶ X.left) [Etale (i ≫ h.left)] :
    IsDominant h.left ∧ ∃ U : T.left.Opens,
      Dense (U : Set T.left) ∧ Smooth (h.left ∣_ U) := by
  letI : IsDominant (i ≫ h.left) :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace (i ≫ h.left) (i ≫ h.left).isOpenMap⟩
  letI : IsDominant h.left := IsDominant.of_comp i h.left
  exact ⟨inferInstance, gfs_exists_smooth_over_dense_open X.hom T.hom h.left (Over.w h)⟩

end HodgeLean.Foundations.Program
