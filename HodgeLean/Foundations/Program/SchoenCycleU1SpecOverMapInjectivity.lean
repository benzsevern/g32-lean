import HodgeLean.Foundations.Program.SchoenCycleU1SpecOver

/-! # Recovery of complex algebra maps from actual affine scheme maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual affine complex scheme maps determine their specified complex
algebra homomorphisms.
Source: Hartshorne, Algebraic Geometry, II.2; Mathlib, `Spec.map_inj`. -/
theorem s2e_u1_specOverMap_injective
    {A C : Type} [CommRing A] [CommRing C] [Algebra ℂ A] [Algebra ℂ C] :
    Function.Injective (s2e_u1_specOverMap (A := A) (B := C)) := by
  intro φ ψ h
  have hs := congrArg Over.Hom.left h
  simp only [s2e_u1_specOverMap, Over.homMk_left] at hs
  rw [Spec.map_inj] at hs
  apply AlgHom.ext
  intro a
  exact congrArg (fun g : CommRingCat.of A ⟶ CommRingCat.of C => g.hom a) hs

end HodgeLean.Foundations.Program
