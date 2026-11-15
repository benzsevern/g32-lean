import HodgeLean.Foundations.Program.G32SelectedRealizationOrbitInversion
import HodgeLean.Foundations.Program.RiemannSurfaceQuotient

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Double-coset representatives give distinct subgroup orbits in a fixed group orbit. -/
theorem s0_orbit_representatives_injective {G X : Type} [Group G] [MulAction G X]
    (H : Subgroup G) (x : X) (g : G)
    (hg : MulAction.stabilizer G x = Subgroup.zpowers g) :
    Function.Injective (fun q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)) ↦
      rsq_proj H X (q.out.out⁻¹ • x)) := by
  obtain ⟨e, he⟩ := g32y_orbit_inversion_equiv H x g hg
  have hv (q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) :
      e q = Quotient.mk'' (⟨q.out.out⁻¹ • x,
        MulAction.mem_orbit_iff.mpr ⟨q.out.out⁻¹, rfl⟩⟩ : MulAction.orbit G x) := by
    have hh := he q.out.out
    simpa only [Quotient.out_eq'] using hh
  intro q q' hq
  apply e.injective
  rw [hv, hv]
  apply Quotient.sound
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hq)
  exact MulAction.mem_orbit_iff.mpr ⟨h, Subtype.ext hh⟩

#print axioms s0_orbit_representatives_injective
end HodgeLean.Foundations.Program
