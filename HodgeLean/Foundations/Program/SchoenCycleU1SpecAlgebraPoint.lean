import HodgeLean.Foundations.Program.SchoenCycleU1SectionEvaluation
import HodgeLean.Foundations.Program.SchoenCycleU1SpecOver

/-! # Actual complex points from affine complex algebra evaluations -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A complex algebra evaluation gives its actual point of the specified affine
scheme over the complex base.
Source: Hartshorne, Algebraic Geometry, II.2, points and algebra homomorphisms. -/
def s2e_u1_specAlgebraPoint (A : Type) [CommRing A] [Algebra ℂ A]
    (e : A →ₐ[ℂ] ℂ) : ComplexPoint (s2e_u1_specOver A) := by
  refine Over.homMk (Spec.map (CommRingCat.ofHom e.toRingHom)) ?_
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) = 𝟙 _
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap ℂ A) ≫
      CommRingCat.ofHom e.toRingHom = 𝟙 (CommRingCat.of ℂ) := by
    ext a
    exact e.commutes a
  rw [he, Spec.map_id]

end HodgeLean.Foundations.Program
