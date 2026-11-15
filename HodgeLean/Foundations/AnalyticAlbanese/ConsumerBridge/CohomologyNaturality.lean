import HodgeLean.Foundations.AnalyticAlbanese.ConsumerBridge.CocyclePullback
import HodgeLean.Adapters.HolomorphicPeriodsComparisonProofs

/-! # Naturality of actual singular scalar extension
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Simplicial
open HodgeLean.Adapters
open scoped TensorProduct Simplicial
namespace HodgeLean.Foundations.AnalyticAlbanese.ConsumerBridge

/-- Scalar extension of an actual cocycle commutes with its original continuous pullback.
HC no distance; AV milestone no distance. -/
theorem cocycleBaseChange_pullback {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (ψ : Cocycle ℚ (TopCat.toSSet.obj Y) n) :
    cocycleBaseChange (TopCat.toSSet.obj X) n (actualCocyclePullback ℚ f n ψ) =
      actualCocyclePullback ℂ f n (cocycleBaseChange (TopCat.toSSet.obj Y) n ψ) := by
  apply Subtype.ext
  apply cochain_ext_chainOfSimplex
  intro σ
  change cochainBaseChange _ n (cochainMap ℚ (TopCat.toSSet.map f) n ψ.val)
      (chainOfSimplex ℂ σ) =
    cochainMap ℂ (TopCat.toSSet.map f) n (cochainBaseChange _ n ψ.val)
      (chainOfSimplex ℂ σ)
  simp only [cochainBaseChange_chainOfSimplex, cochainMap_apply, chainOfSimplex_map]

/-- Complex scalar extension respects the original singular cohomology pullback.
HC no distance; AV milestone no distance. -/
theorem cohomologyBaseChange_natural {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (ξ : ℂ ⊗[ℚ] AlgebraicTopology.Singular.Cohomology ℚ Y n) :
    cohomologyBaseChange X n ((AlgebraicTopology.Singular.cohomologyMap ℚ n f).baseChange ℂ ξ) =
      AlgebraicTopology.Singular.cohomologyMap ℂ n f (cohomologyBaseChange Y n ξ) := by
  induction ξ using TensorProduct.inductionOn with
  | tmul a c =>
    obtain ⟨ψ, rfl⟩ := Singular.cohomologyClass_surjective Y n c
    have h : cohomologyBaseChange X n
        ((AlgebraicTopology.Singular.cohomologyMap ℚ n f).baseChange ℂ
          ((1 : ℂ) ⊗ₜ[ℚ] Singular.cohomologyClass Y n ψ)) =
        AlgebraicTopology.Singular.cohomologyMap ℂ n f
          (cohomologyBaseChange Y n ((1 : ℂ) ⊗ₜ[ℚ] Singular.cohomologyClass Y n ψ)) := by
      rw [LinearMap.baseChange_tmul, actualCocyclePullback_class,
        spec_cohomologyBaseChange_tmul_cohomologyClass_aux X n
          (actualCocyclePullback ℚ f n ψ) (cocycleBaseChange _ n (actualCocyclePullback ℚ f n ψ)) rfl,
        spec_cohomologyBaseChange_tmul_cohomologyClass_aux Y n ψ (cocycleBaseChange _ n ψ) rfl,
        actualCocyclePullback_class, cocycleBaseChange_pullback]
    have ha := congrArg (fun z => a • z) h
    simpa only [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using ha
  | add x y hx hy => simp only [map_add, hx, hy]

end HodgeLean.Foundations.AnalyticAlbanese.ConsumerBridge
