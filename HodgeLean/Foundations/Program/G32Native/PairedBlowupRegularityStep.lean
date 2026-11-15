import HodgeLean.Foundations.Program.G32Native.PairedBlowupIteration
import HodgeLean.Foundations.Program.SchoenTowerConormalDefs
import HodgeLean.Foundations.Program.G32Native.PairedBlowupIntersectionRegularity
import HodgeLean.Foundations.Program.G32Native.NativeBlowupProjective

/-! Regularity interface for a blow-up of an intersection of two branch divisors. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Blowing up a transverse pair preserves regularity of all strict-transform intersections.
Source: Hartshorne, Algebraic Geometry, II, Theorem 8.24 (smooth blow-up)
and its transverse-coordinate calculation; II, Proposition 7.13 (invertible pulled ideal);
Fulton, Intersection Theory, Appendix B.6, the coordinate charts for a smooth centre.
The strict transforms here are the reduced closures used by the native tower. -/
theorem g32l4_paired_blowup_regularity_aux
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Over (Spec ↧ℂ))
    [Smooth B.hom] [IsProjective B.hom] [IsIntegral B.left]
    (D : ι → B.left.IdealSheafData) (u v : ι) (huv : u ≠ v)
    (hintersections : ∀ J : Finset ι,
      Smooth (s2c_subscheme B (J.sup D)).hom ∧
      ∀ x : (s2c_subscheme B (J.sup D)).left,
        ∃ U : (s2c_subscheme B (J.sup D)).left.Opens, x ∈ U ∧
          Nonempty (Scheme.Modules.restrict
            (s2c_conormal (s2c_subschemeι B (J.sup D)).left) U.ι ≅
            (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) :
              U.toScheme.Modules))) :
    let K := D u ⊔ D v
    let B' : Over (Spec ↧ℂ) := Over.mk (K.blowUpπ ≫ B.hom)
    let D' := fun j => s2c_strictTransform K.blowUpπ (D j) K
    (Smooth B'.hom ∧ IsProjective B'.hom ∧ IsIntegral B'.left) ∧
    ∀ J : Finset ι,
      Smooth (s2c_subscheme B' (J.sup D')).hom ∧
      ∀ x : (s2c_subscheme B' (J.sup D')).left,
        ∃ U : (s2c_subscheme B' (J.sup D')).left.Opens, x ∈ U ∧
          Nonempty (Scheme.Modules.restrict
            (s2c_conormal (s2c_subschemeι B' (J.sup D')).left) U.ι ≅
            (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin J.card) :
              U.toScheme.Modules)) := by
  have h := g32l4_paired_blowup_intersection_regularity B D u v hintersections
  exact ⟨⟨h.1.1, g32l4_native_blowUp_projective B (D u ⊔ D v), h.1.2⟩, h.2⟩

end HodgeLean.Foundations.Program
