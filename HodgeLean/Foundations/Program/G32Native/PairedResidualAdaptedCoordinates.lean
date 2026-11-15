import HodgeLean.Foundations.Program.SchoenCycleS3Coordinates
import HodgeLean.Foundations.Program.SchoenCycleS3IdealIsoTransport
import HodgeLean.Foundations.Program.SchoenCycleS3LinearPoints

/-! # A single scheme coordinate change for all actual coefficient hyperplanes -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The actual residue-coordinate hyperplane in the supplied fixed projective parameter space. -/
def residualCoefficientHyperplane
    (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (k r : ℕ) (hd : Module.finrank ℂ (M × (Fin r → ℂ)) = k + 1) (j : Fin r) :
    (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).IdealSheafData :=
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let ep := s2e_finiteDimensionalProjectivePointEquiv (V := M × (Fin r → ℂ)) k hd
  Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure
    (Point.underlying '' {R : ComplexPoint PP | ∃ (v : M × (Fin r → ℂ)) (hv : v ≠ 0),
      ep.symm R = Projectivization.mk ℂ v hv ∧ v.2 j = 0}))

/-- One actual projective scheme automorphism adapts all residue hyperplanes simultaneously. -/
theorem residual_coefficient_hyperplanes_adapted
    (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (k r : ℕ) (hd : Module.finrank ℂ (M × (Fin r → ℂ)) = k + 1) :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    ∃ (e : PP ≅ PP) (ι : Fin r ↪ Fin (k + 1)),
      ∀ j, (residualCoefficientHyperplane M k r hd j).comap e.hom.left =
        s2e_s2b_residueIdeal k (ι j) := by
  dsimp only
  obtain ⟨b, ι, hb⟩ := s2e_residue_adapted_coefficients M k r hd
  let a := b.trans (Module.finBasisOfFinrankEq ℂ (M × (Fin r → ℂ)) hd).equivFun
  refine ⟨s2e_linearProjectiveOverIso a, ι, ?_⟩
  intro j
  let L : (M × (Fin r → ℂ)) →ₗ[ℂ] ℂ :=
    (LinearMap.proj j).comp (LinearMap.snd ℂ _ _)
  exact s2e_coefficient_ideal_transport k hd b L (ι j) (fun v => hb v j)
    (s2e_linearProjectiveOverIso a) (fun v hv => s2e_linearProjectiveOverIso_point a v hv)

#print axioms residualCoefficientHyperplane
#print axioms residual_coefficient_hyperplanes_adapted
end HodgeLean.Foundations.Program.G32Native
