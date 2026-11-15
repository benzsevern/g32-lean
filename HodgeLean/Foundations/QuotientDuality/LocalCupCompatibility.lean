import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeLean.Foundations.Singular.Cup

/-! Compatibility of the cap evaluation construction with singular cup. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

private theorem cap_dual_evaluation (X : TopCat.{0}) (p q : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p)
    (b : Cohomology ℚ X q) (c : Homology ℚ X (p + q)) :
    cohomologyEquivDualHomology ℚ X (p + q)
      (HodgeLean.Foundations.Singular.cup X rfl
        (HodgeLean.Foundations.Singular.cohomologyClass X p φ) b) c =
      cohomologyEquivDualHomology ℚ X q b (capHomologyMap ℚ X p q φ c) := by
  let K := SingularChainComplex ℚ X
  let e (n : ℕ) := HomologicalComplex.linearDualCochainComplexScIso K n
  let F := AlgebraicTopology.Simplicial.capShortComplexHom ℚ p q φ.1 φ.2
  let D := (e q).hom ≫ ShortComplex.linearDualMap F ≫ (e (p + q)).inv
  have hD : (ShortComplex.homologyMap D).hom =
      HodgeLean.Foundations.Singular.cup X rfl
        (HodgeLean.Foundations.Singular.cohomologyClass X p φ) := by
    have h := HodgeLean.Foundations.Singular.homologyMap_cup_left X q p (p + q)
      rfl φ (1 : ℚ) D ?_
    · simpa only [one_smul] using h
    · intro ψ
      have hF : F.τ₂ = AlgebraicTopology.Simplicial.capHom ℚ p q φ.1 :=
        AlgebraicTopology.Simplicial.capShortComplexHom_τ₂ ℚ p q φ.1 φ.2
      dsimp only [D, e]
      simp only [ShortComplex.comp_τ₂, ShortComplex.linearDualMap, hF]
      dsimp [HomologicalComplex.linearDualCochainComplexScIso,
        HomologicalComplex.isoSc', HomologicalComplex.natIsoSc']
      change ψ.comp (AlgebraicTopology.Simplicial.capHom ℚ p q φ.1).hom = _
      simp only [one_smul, Iso.refl_hom,
        ModuleCat.hom_id, LinearMap.comp_id]
      rfl
  rw [← hD]
  change (K.sc (p + q)).linearDualHomologyEquiv
      ((ShortComplex.homologyMap (e (p + q)).hom).hom
        ((ShortComplex.homologyMap D).hom b)) c =
    (K.sc q).linearDualHomologyEquiv
      ((ShortComplex.homologyMap (e q).hom).hom b)
      ((ShortComplex.homologyMap F).hom c)
  have hcomp : D ≫ (e (p + q)).hom = (e q).hom ≫ ShortComplex.linearDualMap F := by
    simp only [D, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hm := congrArg (fun (f : K.linearDualCochainComplex.sc q ⟶ (K.sc (p + q)).linearDual) =>
    (ShortComplex.homologyMap f).hom b) hcomp
  simp only [ShortComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hm
  rw [hm]
  exact LinearMap.congr_fun (ShortComplex.linearDualHomologyEquiv_naturality F
    ((ShortComplex.homologyMap (e q).hom).hom b)) c

theorem localTraceCup_eq_singularCup (X : TopCat.{0}) (p q : ℕ)
    (a : Cohomology ℚ X p) (b : Cohomology ℚ X q) :
    localTraceCup X p q a b = HodgeLean.Foundations.Singular.cup X rfl a b := by
  obtain ⟨φ, rfl⟩ := HodgeLean.Foundations.Singular.cohomologyClass_surjective X p a
  apply (cohomologyEquivDualHomology ℚ X (p + q)).injective
  ext c
  change cohomologyEquivDualHomology ℚ X (p + q)
    ((cohomologyEquivDualHomology ℚ X (p + q)).symm _) c = _
  rw [LinearEquiv.apply_symm_apply]
  change localTracePairing X p q c
      (HodgeLean.Foundations.Singular.cohomologyClass X p φ) b = _
  rw [cap_dual_evaluation]
  change cohomologyEquivDualHomology ℚ X q b
    (capCohomologyLinear ℚ X p q
      ((cochainCohomologyEquiv ℚ X p).symm
        (HodgeLean.Foundations.Singular.cohomologyClass X p φ)) c) = _
  have hclass : HodgeLean.Foundations.Singular.cohomologyClass X p φ =
      cochainCohomologyEquiv ℚ X p
        (((SingularChainComplex ℚ X).sc p).linearDual.moduleCatHomologyClass
          ⟨φ.1, by
            change (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).d
              ((ComplexShape.down ℕ).prev p) p).hom.dualMap φ.1 = 0
            rw [ChainComplex.prev]
            exact φ.2⟩) := rfl
  rw [hclass, LinearEquiv.symm_apply_apply]
  change cohomologyEquivDualHomology ℚ X q b
    (AlgebraicTopology.Simplicial.capCohomologyLinear ℚ p q
      (((SingularChainComplex ℚ X).sc p).linearDual.moduleCatHomologyIso.inv.hom
        (Submodule.Quotient.mk _)) c) = _
  erw [AlgebraicTopology.Simplicial.capCohomologyLinear_on_cycle]
  rfl

#print axioms localTraceCup_eq_singularCup
end HodgeLean.Foundations.QuotientDuality
