import HodgeLean.Foundations.Program.G32Native.PairedResidualIntersectionIdentificationC
import HodgeLean.Ported.Hironaka.Scheme.Smooth.AdaptedCoordinates

/-! # Relative dimension of the actual centre-slice intersection -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The ideal sum in the ambient scheme has the smooth relative dimension
of the specified pulled-back subscheme of the slice.
Source: Hartshorne, Algebraic Geometry, II.3, II.5 and III.10. -/
theorem paired_c3_intersection_relative_dimension
    {K : Type} [Field K] {P V : Over (Spec (CommRingCat.of K))}
    (i : P ⟶ V) [IsClosedImmersion i.left]
    (J : V.left.IdealSheafData) (H : P.left.IdealSheafData)
    (hH : J.comap i.left = H) (m : ℕ)
    [SmoothOfRelativeDimension m (H.subschemeι ≫ P.hom)] :
    SmoothOfRelativeDimension m ((i.left.ker ⊔ J).subschemeι ≫ V.hom) := by
  obtain ⟨e, he⟩ := FibreC.residualIntersection_iso_of_comap_eq i J H hH
  have hfac : (residualIntersection i J).hom =
      e.hom ≫ (H.subschemeι ≫ P.hom) := by
    rw [← Category.assoc, he]
    exact (Over.w (residualIntersectionFirst i J)).symm
  change SmoothOfRelativeDimension m (residualIntersection i J).hom
  rw [hfac]
  simpa only [zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + m) (e.hom ≫ (H.subschemeι ≫ P.hom)))

#print axioms paired_c3_intersection_relative_dimension
end HodgeLean.Foundations.Program.G32Native
