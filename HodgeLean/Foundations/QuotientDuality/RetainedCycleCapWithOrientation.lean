import HodgeLean.Foundations.QuotientDuality.RetainedCycleCupCapEvaluation

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
open AlgebraicTopology.Simplicial
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Cap with the specified actual global class in the repository's singular cohomology model. -/
def retainedCapWithOrientation (X : TopCat.{0}) (p q : ℕ)
    (c : Homology ℚ X (p + q)) : Cohomology ℚ X p →ₗ[ℚ] Homology ℚ X q :=
  ((Simplicial.capCohomologyLinear ℚ p q).comp
    (cochainCohomologyEquiv ℚ X p).symm.toLinearMap).flip c

/-- On represented classes the orientation cap map is the actual cocycle cap map. -/
theorem retained_cap_with_orientation_on_class (X : TopCat.{0}) (p q : ℕ)
    (c : Homology ℚ X (p + q))
    (φ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p) :
    retainedCapWithOrientation X p q c
      (HodgeLean.Foundations.Singular.cohomologyClass X p φ) =
      Simplicial.capHomologyMap ℚ p q φ.1 φ.2 c := by
  let S := (SingularChainComplex ℚ X).sc p
  let φ' : LinearMap.ker S.f.hom.dualMap := ⟨φ.1, by
    change (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).d
      ((ComplexShape.down ℕ).prev p) p).hom.dualMap φ.1 = 0
    rw [ChainComplex.prev]
    exact φ.2⟩
  have he : (cochainCohomologyEquiv ℚ X p).symm
      (HodgeLean.Foundations.Singular.cohomologyClass X p φ) =
      S.linearDual.moduleCatHomologyClass φ' := by
    change (cochainCohomologyEquiv ℚ X p).symm
      ((cochainCohomologyEquiv ℚ X p) (S.linearDual.moduleCatHomologyClass φ')) = _
    exact LinearEquiv.symm_apply_apply _ _
  change Simplicial.capCohomologyLinear ℚ p q
    ((cochainCohomologyEquiv ℚ X p).symm
      (HodgeLean.Foundations.Singular.cohomologyClass X p φ)) c = _
  rw [he]
  exact LinearMap.congr_fun (Simplicial.capCohomologyLinear_on_cycle ℚ p q φ') c

/-- Cup evaluation against the specified orientation equals evaluation on its actual cap map. -/
theorem retained_orientation_cap_evaluation (X : TopCat.{0}) (p q : ℕ)
    (c : Homology ℚ X (p + q)) (a : Cohomology ℚ X p) (b : Cohomology ℚ X q) :
    cohomologyEquivDualHomology ℚ X (p + q)
      (HodgeLean.Foundations.Singular.cup X rfl a b) c =
      cohomologyEquivDualHomology ℚ X q b (retainedCapWithOrientation X p q c a) := by
  obtain ⟨φ, rfl⟩ := HodgeLean.Foundations.Singular.cohomologyClass_surjective X p a
  exact (retained_cup_cap_evaluation X p q φ b c).trans
    (congrArg (fun z => cohomologyEquivDualHomology ℚ X q b z)
      (retained_cap_with_orientation_on_class X p q c φ).symm)

/-- The orientation cap evaluation identity retains the specified target-degree equality. -/
theorem retained_orientation_cap_evaluation_cast (X : TopCat.{0}) (p q n : ℕ)
    (h : p + q = n) (c : Homology ℚ X n)
    (a : Cohomology ℚ X p) (b : Cohomology ℚ X q) :
    cohomologyEquivDualHomology ℚ X n
      (HodgeLean.Foundations.Singular.cup X h a b) c =
      cohomologyEquivDualHomology ℚ X q b
        (retainedCapWithOrientation X p q (h.symm ▸ c) a) := by
  subst n
  exact retained_orientation_cap_evaluation X p q c a b

end HodgeLean.Foundations.QuotientDuality
