import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateInclusionMorphisms
import HodgeLean.Foundations.Program.G32Native.PairedC3SourceFixedLinearCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectivePointExt

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] PairedC3ProjectiveFactorCoordinates.targetAdd
  PairedC3ProjectiveFactorCoordinates.targetModule PairedC3ProjectiveFactorCoordinates.targetFinite

/-- A retained linear parameterization can be normalized on its literal source. -/
theorem paired_c3_factor_coordinate_normalization {k n : ℕ}
    (i : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) ⟶
      ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ))
    (C : PairedC3ProjectiveFactorCoordinates k n _ i)
    (j : Fin (k + 1) ↪ Fin (n + 1)) :
    ∃ e : ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ) ≅
        ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ),
      i ≫ e.hom = (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).inv ≫
        pairedC3PolynomialCoordinateInclusion (A := ℂ) j ≫
        (s2_polynomialProjectiveSpaceIso ℂ (Fin (n + 1))).hom := by
  letI : IsIntegral (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).left :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral k
  letI : (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)).IsSeparated := by
    constructor
    rw [← CategoryTheory.Limits.terminal.comp_from
      (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))]
    infer_instance
  let b := (Module.finBasisOfFinrankEq ℂ C.targetSpace C.targetDimension).equivFun
  let f := b.toLinearMap.comp C.embedding
  have hf : Function.Injective f := b.injective.comp C.embedding_injective
  obtain ⟨a, ha⟩ := paired_c3_source_fixed_ambient_coordinates f
    (pairedC3CoordinateVectorLift j) hf (paired_c3_coordinate_vector_lift_injective j)
  let e := C.ambient.symm ≪≫ s2e_linearProjectiveSpaceIso a
  refine ⟨e, ?_⟩
  apply paired_c3_hom_ext_of_complex_points
    (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
  intro p
  obtain ⟨l, rfl⟩ := (s2e_projectivePointHomeomorph k).surjective p
  induction l using Projectivization.ind with
  | h u hu =>
    change (vectorToComplexPoint u hu).left ≫ (i ≫ e.hom) = _
    rw [← Category.assoc, C.point_formula]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    change (vectorToComplexPoint (f u) (fun h => hu (hf (h.trans (map_zero f).symm)))).left ≫
      (s2e_linearProjectiveOverIso a).hom.left = _
    have hpoint := ComplexPoint.underlying_injective_of_locallyOfFiniteType
      (X := Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))
      (show (Point.map (s2e_linearProjectiveOverIso a).hom
          (vectorToComplexPoint (f u) (fun h => hu (hf (h.trans (map_zero f).symm))))).underlying =
        (vectorToComplexPoint (a (f u)) (a.map_ne_zero_iff.mpr (fun h => hu (hf (h.trans (map_zero f).symm))))).underlying from
        s2e_linearProjectiveOverIso_point a (f u) _)
    have hp := congrArg (fun p => p.left) hpoint
    change (vectorToComplexPoint (f u) _).left ≫
      (s2e_linearProjectiveOverIso a).hom.left = _ at hp
    rw [hp]
    change (vectorToComplexPoint (a (f u)) _).left = (vectorToComplexPoint u hu).left ≫ _
    simpa only [ha u] using (paired_c3_coordinate_inclusion_point_morphism j u hu).symm

#print axioms paired_c3_factor_coordinate_normalization
end HodgeLean.Foundations.Program.G32Native
