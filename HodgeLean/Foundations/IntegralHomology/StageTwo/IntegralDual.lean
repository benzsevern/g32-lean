import HodgeLean.Foundations.IntegralHomology.StageTwo.Evaluation
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Integral quotient evaluation from explicit retractions of cycles and boundaries.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

theorem explicitPairing_bijective_of_retractions {R : Type} [CommRing R]
    (S : ShortComplex (ModuleCat R))
    (p : S.X₂ →ₗ[R] LinearMap.ker S.g.hom)
    (hp : ∀ z : LinearMap.ker S.g.hom, p z = z)
    (r : S.X₃ →ₗ[R] LinearMap.range S.g.hom)
    (hr : ∀ z : LinearMap.range S.g.hom, r z = z) :
    Function.Bijective S.dualHomologyComparisonExplicit := by
  constructor
  · intro a b hab
    induction a using Submodule.Quotient.induction_on with
    | H phi =>
      induction b using Submodule.Quotient.induction_on with
      | H psi =>
        rw [Submodule.Quotient.eq]
        have hzero : S.dualCycleToHomologyFunctional (phi - psi) = 0 :=
          (S.dualCycleToHomologyFunctional.map_sub phi psi).trans (sub_eq_zero.mpr hab)
        have hv : (phi - psi).val ∈ (LinearMap.ker S.g.hom).dualAnnihilator := by
          rw [Submodule.mem_dualAnnihilator]
          intro z hz
          exact LinearMap.congr_fun hzero (Submodule.Quotient.mk ⟨z, hz⟩)
        have hs : Function.Surjective (LinearMap.range S.g.hom).subtype.dualMap := by
          intro u
          refine ⟨u.comp r, ?_⟩
          ext z
          exact congrArg u (hr z)
        rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective
          S.g.hom hs] at hv
        obtain ⟨eta, heta⟩ := hv
        exact ⟨eta, Subtype.ext heta⟩
  · intro u
    let phi : Module.Dual R S.X₂ :=
      (u.comp (LinearMap.range S.moduleCatToCycles).mkQ).comp p
    have hphi : phi ∈ LinearMap.ker S.f.hom.dualMap := by
      apply LinearMap.mem_ker.mpr
      ext x
      have hx : p (S.f.hom x) = S.moduleCatToCycles x :=
        hp (S.moduleCatToCycles x)
      change u (Submodule.Quotient.mk (p (S.f.hom x))) = 0
      rw [hx, (Submodule.Quotient.mk_eq_zero _).mpr (S.moduleCatToCycles.mem_range_self x),
        map_zero]
    refine ⟨Submodule.Quotient.mk ⟨phi, hphi⟩, ?_⟩
    ext z
    induction z using Submodule.Quotient.induction_on with
    | H z =>
      change phi z.val = u (Submodule.Quotient.mk z)
      change u (Submodule.Quotient.mk (p z.val)) = _
      rw [hp]
end HodgeLean.Foundations.IntegralHomology.StageTwo
