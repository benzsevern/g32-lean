import HodgeLean.Foundations.IntegralHomology.StageTwo.IntegralDual

/-! Functionals to a domain factor through the torsion quotient.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

theorem dual_vanishes_torsion {R M : Type} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] (u : Module.Dual R M) :
    Submodule.torsion R M ≤ LinearMap.ker u := by
  intro a ha
  obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff a).mp ha
  have hr' : (r : R) • a = 0 := hr
  have hz : (r : R) • u a = 0 := by
    rw [← map_smul, hr', map_zero]
  exact (smul_eq_zero.mp hz).resolve_left (nonZeroDivisors.coe_ne_zero r)

def torsionQuotientDual {R M : Type} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] :
    Module.Dual R M ≃ₗ[R] Module.Dual R (M ⧸ Submodule.torsion R M) :=
  (LinearEquiv.ofBijective (Submodule.torsion R M).mkQ.dualMap
    ⟨LinearMap.dualMap_injective_of_surjective (Submodule.mkQ_surjective _),
      fun u => ⟨(Submodule.torsion R M).liftQ u (dual_vanishes_torsion u), by
        ext a
        rfl⟩⟩).symm

theorem torsionQuotientDual_apply {R M : Type} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] (u : Module.Dual R M) (a : M) :
    torsionQuotientDual u (Submodule.Quotient.mk a) = u a := by
  have h := (torsionQuotientDual (R := R) (M := M)).symm_apply_apply u
  exact LinearMap.congr_fun h a
end HodgeLean.Foundations.IntegralHomology.StageTwo
