import HodgeLean.Foundations.Program.G32Native.PairedResidualNativeStalkSmooth
import HodgeLean.Foundations.Program.G32Native.PairedResidualTargetStalkSmooth
import HodgeLean.Foundations.Program.G32Native.PairedResidualSmoothDetection

/-! # Smoothness of the original morphism from its native differential -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Surjectivity in the original native charts puts the specified complex
point in the smooth locus of the actual scheme morphism.
Source: EGA IV, 17.11.1; Hartshorne, Algebraic Geometry, II.8. -/
theorem residual_native_submersion_mem_smoothLocus
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f.left] (p : ComplexPoint X)
    (ht : Function.Surjective (fderiv ℂ (fun z : Fin d → ℂ =>
      localChart Y e (Point.map f p)
        (Point.map f ((localChart X d p).symm (localChart X d p p + z)))) 0)) :
    p.underlying ∈ f.left.smoothLocus := by
  let DX := localEtaleCoordinates X d p
  let DY := localEtaleCoordinates Y e (Point.map f p)
  let U := DX.neighborhood ⊓ f.left ⁻¹ᵁ DY.neighborhood
  have hpU : p.underlying ∈ U := ⟨DX.mem, DY.mem⟩
  obtain ⟨_, ⟨W, hWa, rfl⟩, hpW, hWU⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open hpU U.isOpen
  have hWX : W ≤ DX.neighborhood := fun x hx => (hWU hx).1
  have hWY : W ≤ f.left ⁻¹ᵁ DY.neighborhood := fun x hx => (hWU hx).2
  apply Scheme.Hom.mem_smoothLocus.mpr
  apply residual_formallySmooth_target_stalk f.left p.underlying
    ⟨DY.neighborhood, DY.isAffine⟩ W hpW DY.mem hWY
  letI : Algebra Γ(Y.left, DY.neighborhood) (X.left.presheaf.stalk p.underlying) :=
    (f.left.appLE DY.neighborhood W hWY ≫ X.left.presheaf.germ W p.underlying hpW).hom.toAlgebra
  exact RingHom.formallySmooth_algebraMap.mpr
    (residual_native_stalk_formallySmooth X Y d e f p ⟨W, hWa⟩ hpW hWX hWY ht)

#print axioms residual_native_submersion_mem_smoothLocus
end HodgeLean.Foundations.Program.G32Native
