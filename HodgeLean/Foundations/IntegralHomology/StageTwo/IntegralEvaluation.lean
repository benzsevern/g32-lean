import HodgeLean.Foundations.IntegralHomology.StageTwo.HomologyZero
import HodgeLean.Foundations.IntegralHomology.StageTwo.TorsionDual

/-! Degree-one integral evaluation using free singular chains and free degree-zero homology.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

theorem integralEvaluation_bijective (X : TopCat.{0}) :
    Function.Bijective (evaluation ℤ X) := by
  let S := (SingularChainComplex ℤ X).sc 1
  letI : Module.Free ℤ S.X₃ :=
    Module.Free.of_equiv (chainGroupFinsuppIso ℤ X ((ComplexShape.down ℕ).next 1)).toLinearEquiv.symm
  letI : Module ℤ (LinearMap.range S.g.hom) := (LinearMap.range S.g.hom).module
  letI : Module ℤ (S.X₃ ⧸ LinearMap.range S.g.hom) := Submodule.Quotient.module _
  have hq (k : ℕ) (hk : k = 0) :
      Module.Free ℤ ((ZChains X).X k ⧸ LinearMap.range ((ZChains X).d 1 k).hom) := by
    subst k
    exact integralBoundaryQuotient_free X
  have h := hq _ (ChainComplex.next_nat_succ 0)
  have hmod : Submodule.Quotient.module
      (LinearMap.range ((ZChains X).d 1 ((ComplexShape.down ℕ).next 1)).hom) =
      AddCommGroup.toIntModule ((ZChains X).X ((ComplexShape.down ℕ).next 1) ⧸
        LinearMap.range ((ZChains X).d 1 ((ComplexShape.down ℕ).next 1)).hom) :=
    Subsingleton.elim _ _
  rw [← hmod] at h
  haveI : Module.Free ℤ (S.X₃ ⧸ LinearMap.range S.g.hom) := h
  obtain ⟨r, hr⟩ := submodule_retraction (LinearMap.range S.g.hom)
  haveI : Module.Projective ℤ (LinearMap.range S.g.hom) :=
    Module.Projective.of_split (LinearMap.range S.g.hom).subtype r (by
      ext z
      exact congrArg Subtype.val (hr z))
  obtain ⟨p, hp⟩ := kernel_retraction S.g.hom
  let e := (cochainCohomologyEquiv ℤ X 1).symm.trans
    (S.linearDual.moduleCatHomologyIso.toLinearEquiv.trans
      ((LinearEquiv.ofBijective S.dualHomologyComparisonExplicit
        (explicitPairing_bijective_of_retractions S p hp r hr)).trans
        S.moduleCatHomologyIso.toLinearEquiv.dualMap))
  exact e.bijective
end HodgeLean.Foundations.IntegralHomology.StageTwo
