import HodgeLean.Foundations.Singular.Cup
import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
open AlgebraicTopology.Simplicial
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Universal coefficients evaluate the actual singular cocycle representative on a cycle. -/
theorem retained_cohomology_class_evaluation (X : TopCat.{0}) (n : ℕ)
    (φ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) n)
    (z : LinearMap.ker ((SingularChainComplex ℚ X).sc n).g.hom) :
    cohomologyEquivDualHomology ℚ X n
      (HodgeLean.Foundations.Singular.cohomologyClass X n φ)
      (((SingularChainComplex ℚ X).sc n).moduleCatHomologyClass z) = φ.1 z.1 := by
  let S := (SingularChainComplex ℚ X).sc n
  let φ' : LinearMap.ker S.f.hom.dualMap := ⟨φ.1, by
    change (((SingularChainComplex ℚ X).sc n).f.hom.dualMap) φ.1 = 0
    change (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).d
      ((ComplexShape.down ℕ).prev n) n).hom.dualMap φ.1 = 0
    rw [ChainComplex.prev]
    exact φ.2⟩
  let e := (ShortComplex.homologyMapIso
    (HomologicalComplex.linearDualCochainComplexScIso (SingularChainComplex ℚ X) n)).toLinearEquiv
  change S.linearDualHomologyEquiv (e (e.symm
    (S.linearDual.moduleCatHomologyClass φ'))) (S.moduleCatHomologyClass z) = φ.1 z.1
  rw [e.apply_symm_apply]
  exact ShortComplex.linearDualHomologyEquiv_class_apply_class S φ' z

/-- The actual singular cup evaluation agrees with cap product by a cocycle representative. -/
theorem retained_cup_cap_evaluation (X : TopCat.{0}) (p q : ℕ)
    (φ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p)
    (b : Cohomology ℚ X q) (c : Homology ℚ X (p + q)) :
    cohomologyEquivDualHomology ℚ X (p + q)
      (HodgeLean.Foundations.Singular.cup X rfl
        (HodgeLean.Foundations.Singular.cohomologyClass X p φ) b) c =
      cohomologyEquivDualHomology ℚ X q b
        (Simplicial.capHomologyMap ℚ p q φ.1 φ.2 c) := by
  let C := SingularChainComplex ℚ X
  let F := Simplicial.capShortComplexHom ℚ p q φ.1 φ.2
  let iQ := HomologicalComplex.linearDualCochainComplexScIso C q
  let iN := HomologicalComplex.linearDualCochainComplexScIso C (p + q)
  let f := iQ.hom ≫ ShortComplex.linearDualMap F ≫ iN.inv
  have hcup := HodgeLean.Foundations.Singular.homologyMap_cup_left X q p (p + q)
    rfl φ (1 : ℚ) f (by
      intro ψ
      have hF : F.τ₂ = Simplicial.capHom ℚ p q φ.1 :=
        Simplicial.capShortComplexHom_τ₂ ℚ p q φ.1 φ.2
      simp only [f, ShortComplex.comp_τ₂, ShortComplex.linearDualMap, hF]
      change ψ.comp (Simplicial.cap ℚ p q φ.1) =
        1 • (HodgeLean.Foundations.Singular.cupCochain X p q φ.1 ψ).comp
          (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).XIsoOfEq rfl).hom.hom
      simp only [one_smul, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
        ]
      rfl)
  rw [one_smul] at hcup
  apply Eq.trans (congrArg (fun a => cohomologyEquivDualHomology ℚ X (p + q) a c)
    (LinearMap.congr_fun hcup b).symm)
  have hcomm : f ≫ iN.hom = iQ.hom ≫ ShortComplex.linearDualMap F := by
    simp only [f, Category.assoc, iN.inv_hom_id]
    exact congrArg (fun g : (C.sc q).linearDual ⟶ (C.sc (p + q)).linearDual => iQ.hom ≫ g)
      (Category.comp_id (ShortComplex.linearDualMap F))
  have hh := congrArg (fun g : C.linearDualCochainComplex.sc q ⟶ (C.sc (p + q)).linearDual =>
    (ShortComplex.homologyMap g).hom b) hcomm
  simp only [ShortComplex.homologyMap_comp, ConcreteCategory.comp_apply] at hh
  change (C.sc (p + q)).linearDualHomologyEquiv
    ((ShortComplex.homologyMap iN.hom).hom ((ShortComplex.homologyMap f).hom b)) c =
    (C.sc q).linearDualHomologyEquiv ((ShortComplex.homologyMap iQ.hom).hom b)
      ((ShortComplex.homologyMap F).hom c)
  rw [hh]
  exact congrArg (fun l => l c) (ShortComplex.linearDualHomologyEquiv_naturality F
    ((ShortComplex.homologyMap iQ.hom).hom b))

end HodgeLean.Foundations.QuotientDuality
