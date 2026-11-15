import HodgeLean.Foundations.Singular.Cup
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Cap.Relative

/-! # Evaluation of the cup pairing through the actual cap product -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
lemma properCycle_cup_cap_cocycle
    (X : TopCat.{0}) (p q : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p)
    (u : Cohomology ℚ X q) (c : Homology ℚ X (p + q)) :
    cohomologyEquivDualHomology ℚ X (p + q)
      (cup X rfl (cohomologyClass X p φ) u) c =
    cohomologyEquivDualHomology ℚ X q u (capHomologyMap ℚ X p q φ c) := by
  let K := SingularChainComplex ℚ X
  let eN := HomologicalComplex.linearDualCochainComplexScIso K (p + q)
  let eQ := HomologicalComplex.linearDualCochainComplexScIso K q
  let f := AlgebraicTopology.Simplicial.capShortComplexHom ℚ p q φ.1 φ.2
  let g := eQ.hom ≫ ShortComplex.linearDualMap f ≫ eN.inv
  have hg : (ShortComplex.homologyMap g).hom = cup X rfl (cohomologyClass X p φ) := by
    have h := homologyMap_cup_left X q p (p + q) rfl φ (1 : ℚ) g (fun ψ => by
      simp only [one_smul, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
        ModuleCat.hom_id, LinearMap.comp_id]
      change f.τ₂.hom.dualMap ψ = cupCochain X p q φ.1 ψ
      rw [show f.τ₂ = AlgebraicTopology.Simplicial.capHom ℚ p q φ.1 from
        AlgebraicTopology.Simplicial.capShortComplexHom_τ₂ ℚ p q φ.1 φ.2]
      rfl)
    simpa only [one_smul] using h
  have hmap : ShortComplex.homologyMap g ≫ ShortComplex.homologyMap eN.hom =
      ShortComplex.homologyMap eQ.hom ≫
        ShortComplex.homologyMap (ShortComplex.linearDualMap f) := by
    rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
    simp only [g, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hconj :
      (cochainCohomologyEquiv ℚ X (p + q)).symm
        (cup X rfl (cohomologyClass X p φ) u) =
      (ShortComplex.homologyMap (ShortComplex.linearDualMap f)).hom
        ((cochainCohomologyEquiv ℚ X q).symm u) := by
    rw [← hg]
    exact ConcreteCategory.congr_hom hmap u
  change (K.sc (p + q)).linearDualHomologyEquiv
      ((cochainCohomologyEquiv ℚ X (p + q)).symm
        (cup X rfl (cohomologyClass X p φ) u)) c =
    (K.sc q).linearDualHomologyEquiv ((cochainCohomologyEquiv ℚ X q).symm u)
      ((ShortComplex.homologyMap f).hom c)
  rw [hconj]
  exact LinearMap.congr_fun (ShortComplex.linearDualHomologyEquiv_naturality f _) c

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma properCycle_cap_on_class
    (X : TopCat.{0}) (p q : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p) :
    capCohomologyLinear ℚ X p q
      ((cochainCohomologyEquiv ℚ X p).symm (cohomologyClass X p φ)) =
      capHomologyMap ℚ X p q φ := by
  let S := (SingularChainComplex ℚ X).sc p
  let α : LinearMap.ker S.linearDual.g.hom := ⟨φ.1, by
    change (((SingularChainComplex ℚ X).sc p).f.hom.dualMap) φ.1 = 0
    change (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).d
      ((ComplexShape.down ℕ).prev p) p).hom.dualMap φ.1 = 0
    rw [ChainComplex.prev]
    exact φ.2⟩
  have hφ : cohomologyClass X p φ = cochainCohomologyEquiv ℚ X p
      (S.linearDual.moduleCatHomologyClass α) := rfl
  rw [hφ, LinearEquiv.symm_apply_apply]
  change AlgebraicTopology.Simplicial.capCohomologyLinear ℚ p q
    (S.linearDual.moduleCatHomologyClass α) = _
  exact AlgebraicTopology.Simplicial.capCohomologyLinear_on_cycle ℚ p q α

lemma properCycle_cup_cap
    (X : TopCat.{0}) (p q : ℕ)
    (a : Cohomology ℚ X p) (u : Cohomology ℚ X q)
    (c : Homology ℚ X (p + q)) :
    cohomologyEquivDualHomology ℚ X (p + q) (cup X rfl a u) c =
    cohomologyEquivDualHomology ℚ X q u
      (capCohomologyLinear ℚ X p q ((cochainCohomologyEquiv ℚ X p).symm a) c) := by
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective X p a
  rw [properCycle_cap_on_class]
  exact properCycle_cup_cap_cocycle X p q φ u c

lemma properCycle_cup_degree_transport
    (X : TopCat.{0}) {p q n : ℕ} (h : p + q = n)
    (a : Cohomology ℚ X p) (u : Cohomology ℚ X q) (c : Homology ℚ X n) :
    cohomologyEquivDualHomology ℚ X n (cup X h a u) c =
      cohomologyEquivDualHomology ℚ X (p + q) (cup X rfl a u) (h.symm ▸ c) := by
  subst n
  rfl

end HodgeLean.Foundations.QuotientDuality
