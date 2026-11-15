import HodgeLean.Foundations.QuotientDuality.RetainedCycleDerivedCapLinearity

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Equal actual singular cohomology classes in positive degree differ by an actual coboundary. -/
theorem retained_cocycles_eq_add_coboundary_of_class_eq (X : TopCat.{0}) (p : ℕ)
    (φ ψ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) (p + 1))
    (h : HodgeLean.Foundations.Singular.cohomologyClass X (p + 1) φ =
      HodgeLean.Foundations.Singular.cohomologyClass X (p + 1) ψ) :
    ∃ η : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p,
      φ.1 = ψ.1 + Simplicial.coboundary ℚ p η := by
  let K := SingularChainComplex ℚ X
  let T := (K.sc (p + 1)).linearDual
  let φ' : LinearMap.ker T.g.hom := ⟨φ.1, by
    change ((K.d ((ComplexShape.down ℕ).prev (p + 1)) (p + 1)).hom.dualMap) φ.1 = 0
    rw [ChainComplex.prev]
    exact φ.2⟩
  let ψ' : LinearMap.ker T.g.hom := ⟨ψ.1, by
    change ((K.d ((ComplexShape.down ℕ).prev (p + 1)) (p + 1)).hom.dualMap) ψ.1 = 0
    rw [ChainComplex.prev]
    exact ψ.2⟩
  have hq : (Submodule.Quotient.mk φ' : T.moduleCatLeftHomologyData.H) =
      Submodule.Quotient.mk ψ' := by
    apply T.moduleCatHomologyIso.toLinearEquiv.symm.injective
    apply (cochainCohomologyEquiv ℚ X (p + 1)).injective
    exact h
  rw [Submodule.Quotient.eq] at hq
  obtain ⟨η, hη⟩ := hq
  have he := congrArg (Simplicial.cohomologyCycleToCocycle ℚ (p + 1)) hη
  dsimp only [T, K] at he
  erw [Simplicial.cohomologyCycleToCocycle_moduleCatToCycles_succ ℚ p η] at he
  refine ⟨(η : Module.Dual ℚ (K.X ((ComplexShape.down ℕ).next (p + 1)))).comp
    (K.XIsoOfEq (ChainComplex.next_nat_succ p)).inv.hom, ?_⟩
  have hv := congrArg (fun z : Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) (p + 1) => z.1) he
  change Simplicial.coboundary ℚ p _ = φ.1 - ψ.1 at hv
  erw [hv]
  abel

/-- Actual degree-zero singular cohomology retains its cocycle representative uniquely. -/
theorem retained_cohomology_class_zero_injective (X : TopCat.{0}) :
    Function.Injective (HodgeLean.Foundations.Singular.cohomologyClass (R := ℚ) X 0) := by
  intro φ ψ h
  let K := SingularChainComplex ℚ X
  let T := (K.sc 0).linearDual
  let φ' : LinearMap.ker T.g.hom := ⟨φ.1, by
    change ((K.d ((ComplexShape.down ℕ).prev 0) 0).hom.dualMap) φ.1 = 0
    rw [ChainComplex.prev]
    exact φ.2⟩
  let ψ' : LinearMap.ker T.g.hom := ⟨ψ.1, by
    change ((K.d ((ComplexShape.down ℕ).prev 0) 0).hom.dualMap) ψ.1 = 0
    rw [ChainComplex.prev]
    exact ψ.2⟩
  have hq : (Submodule.Quotient.mk φ' : T.moduleCatLeftHomologyData.H) =
      Submodule.Quotient.mk ψ' := by
    apply T.moduleCatHomologyIso.toLinearEquiv.symm.injective
    apply (cochainCohomologyEquiv ℚ X 0).injective
    exact h
  have hz : T.moduleCatToCycles = 0 := by
    apply LinearMap.ext
    intro η
    apply Subtype.ext
    change ((K.sc 0).g.hom.dualMap) η = 0
    have hg : (K.sc 0).g = 0 := by
      change K.d 0 ((ComplexShape.down ℕ).next 0) = 0
      apply K.shape
      rw [ChainComplex.next_nat_zero]
      simp
    rw [hg]
    ext c
    let ηF : Module.Dual ℚ (K.sc 0).X₃ := η
    change ηF 0 = 0
    exact map_zero ηF
  rw [Submodule.Quotient.eq, hz, LinearMap.range_zero] at hq
  have hc : φ' - ψ' = 0 := hq
  have hv := congrArg (fun z : LinearMap.ker T.g.hom => z.1) hc
  apply Subtype.ext
  exact sub_eq_zero.mp hv

/-- The actual derived cap action depends only on the actual singular cohomology class. -/
theorem retained_derived_cap_eq_of_class_eq (X : TopCat.{0}) (n : ℕ)
    (φ ψ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) n)
    (h : HodgeLean.Foundations.Singular.cohomologyClass X n φ =
      HodgeLean.Foundations.Singular.cohomologyClass X n ψ) :
    retainedDerivedCapAction X n φ.1 φ.2 = retainedDerivedCapAction X n ψ.1 ψ.2 := by
  cases n with
  | zero =>
      have he := retained_cohomology_class_zero_injective X h
      subst ψ
      rfl
  | succ p =>
      obtain ⟨η, hη⟩ := retained_cocycles_eq_add_coboundary_of_class_eq X p φ ψ h
      exact retained_derived_cap_eq_of_eq_add_coboundary X p φ.1 ψ.1 φ.2 ψ.2 η hη

end HodgeLean.Foundations.QuotientDuality
