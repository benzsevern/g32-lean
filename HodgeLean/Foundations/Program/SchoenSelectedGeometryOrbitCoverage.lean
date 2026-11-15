import HodgeLean.Foundations.Program.SchoenSelectedGeometryOrbitRepresentatives

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The local double-coset representatives meet every subgroup orbit in a group orbit. -/
theorem s0_orbit_representatives_cover {G X : Type} [Group G] [MulAction G X]
    (H : Subgroup G) (x : X) (g : G)
    (hg : MulAction.stabilizer G x = Subgroup.zpowers g)
    (y : X) (hy : y ∈ MulAction.orbit G x) :
    ∃ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)),
      rsq_proj H X y = rsq_proj H X (q.out.out⁻¹ • x) := by
  obtain ⟨e, he⟩ := g32y_orbit_inversion_equiv H x g hg
  let z : MulAction.orbit G x := ⟨y, hy⟩
  let q := e.symm (Quotient.mk'' z)
  refine ⟨q, ?_⟩
  have hh := he q.out.out
  have hv : e q = Quotient.mk'' (⟨q.out.out⁻¹ • x,
      MulAction.mem_orbit_iff.mpr ⟨q.out.out⁻¹, rfl⟩⟩ : MulAction.orbit G x) := by
    simpa only [Quotient.out_eq'] using hh
  have hq : e q = Quotient.mk'' z := e.apply_symm_apply _
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact (hq.symm.trans hv))
  apply Quotient.sound
  exact MulAction.mem_orbit_iff.mpr ⟨h, congrArg Subtype.val hh⟩

#print axioms s0_orbit_representatives_cover
end HodgeLean.Foundations.Program
