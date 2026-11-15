import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralLiftRange

/-! Lifted displacements compute the scalar integral homology pairing. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.Program
variable {V J X : Type} [AddCommGroup V] [TopologicalSpace V] [ContinuousAdd V]
    [AddCommGroup J] [TopologicalSpace J] [TopologicalSpace X]
    (π : V →+ J) (hπ : IsCoveringMap π ∧ Function.Surjective π)
    (f : X → J) (hf : Continuous f) (ℓ : V →+ ℂ)

theorem s4_c1a6_liftCocycle_chain :
    s4_c1a6_integralCocycleChain (TopCat.of X) (b3Rest2_liftCocycle π hπ f hf ℓ) =
      ℓ.toIntLinearMap.comp (s4_c1a6_liftChain π hπ f hf) := by
  suffices h : (ModuleCat.ofHom
      (s4_c1a6_integralCocycleChain (TopCat.of X) (b3Rest2_liftCocycle π hπ f hf ℓ)) :
        (s4_c1a6_ZChains (TopCat.of X)).X 1 ⟶ ModuleCat.of ℤ ℂ) =
      ModuleCat.ofHom (ℓ.toIntLinearMap.comp (s4_c1a6_liftChain π hπ f hf)) by
    exact congrArg ModuleCat.Hom.hom h
  apply SSet.chainComplex_hom_ext
  intro σ
  ext
  change (b3Rest2_liftCocycle π hπ f hf ℓ).val
    (s4_c1a6_zToCChainGroup (TopCat.of X) 1
      (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) σ).hom 1)) =
    ℓ (s4_c1a6_simplexLinear (TopCat.of X) 1 (s4_c1a6_liftDisplacement π hπ f hf)
      (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) σ).hom 1))
  rw [s4_c1a6_zToCChainGroup_iota, Int.cast_one]
  erw [s4_c1a6_simplexLinear_iota]
  rw [one_smul]
  exact b3Rest2_liftCocycle_apply π hπ f hf ℓ σ

theorem s4_c1a6_liftCocycle_pairing_cycle
    (z : (s4_c1a6_ZChains (TopCat.of X)).cycles 1) :
    s4_c1a6_integralCocyclePairing (TopCat.of X) (b3Rest2_liftCocycle π hπ f hf ℓ)
      (Submodule.Quotient.mk ((s4_c1a6_ZChains (TopCat.of X)).homologyπ 1 z)) =
      ℓ (s4_c1a6_liftChain π hπ f hf ((s4_c1a6_ZChains (TopCat.of X)).iCycles 1 z)) := by
  rw [s4_c1a6_integralCocyclePairing_cycle]
  exact LinearMap.congr_fun (s4_c1a6_liftCocycle_chain π hπ f hf ℓ) _

end HodgeLean.Foundations.Program
