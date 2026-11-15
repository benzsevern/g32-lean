import HodgeLean.Foundations.Program.G32SelectedRealizationRotationCharacter
import HodgeLean.Foundations.Program.RiemannSurfaceQuotient

noncomputable section
set_option maxHeartbeats 400000
open Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- The character of a positive rotation is constant on subgroup orbits. -/
theorem s0_rotation_character_orbit {C H A : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Group H] [Finite H] [MulAction H C] [FaithfulSMul H C] [CommGroup A]
    (hH : ∀ h : H, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : C ↦ h • z))
    (χ : H →* A) (x y : C) (r s : H)
    (hr : b4_IsRotGen ℂ x r) (hs : b4_IsRotGen ℂ y s)
    (he : Quotient.mk'' x = (Quotient.mk'' y : Quotient (MulAction.orbitRel H C))) :
    χ r = χ s := by
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact he)
  have hc := RiemannRochTop_rotGen_conjugate hH y h s hs
  rw [hh] at hc
  have hu := b4_rotGen_unique (Module.finrank_self ℂ) hH x r (h * s * h⁻¹) hr hc
  rw [hu, map_mul, map_mul, map_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

#print axioms s0_rotation_character_orbit
end HodgeLean.Foundations.Program
