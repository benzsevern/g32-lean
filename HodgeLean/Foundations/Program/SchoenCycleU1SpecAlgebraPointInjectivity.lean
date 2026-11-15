import HodgeLean.Foundations.Program.SchoenCycleU1SpecAlgebraPoint

/-! # Recovery of affine complex evaluations from actual complex points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual complex point of a specified affine scheme determines its
complex algebra evaluation.
Source: Hartshorne, Algebraic Geometry, II.2; Mathlib, `Spec.map_inj`. -/
theorem s2e_u1_specAlgebraPoint_injective
    (A : Type) [CommRing A] [Algebra ℂ A] :
    Function.Injective (s2e_u1_specAlgebraPoint A) := by
  intro e e' h
  have hs := congrArg Over.Hom.left h
  simp only [s2e_u1_specAlgebraPoint, Over.homMk_left] at hs
  rw [Spec.map_inj] at hs
  apply AlgHom.ext
  intro a
  exact congrArg (fun g : CommRingCat.of A ⟶ CommRingCat.of ℂ => g.hom a) hs

end HodgeLean.Foundations.Program
