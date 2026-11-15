import HodgeLean.Foundations.BundleThom.ProductComplementHomologyZeroHelpers

/-! # Relative successor-degree vanishing from adjacent inclusion maps

The actual relative chain sequence retains its boundary map throughout the argument.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Surjectivity and injectivity in adjacent degrees of the actual inclusion force successor-degree relative homology to vanish.
Source: Hatcher, Algebraic Topology, §2.1, the long exact sequence of a pair. -/
theorem i1_relativeHomologySuccessor_isZero (X : TopPair) (n : ℕ)
    [Epi (HomologicalComplex.homologyMap ((chainPairFunctor ℚ).obj X).hom (n + 1))]
    [Mono (HomologicalComplex.homologyMap ((chainPairFunctor ℚ).obj X).hom n)] :
    IsZero (RelativeHomology ℚ X (n + 1)) := by
  let S := relativeChainShortComplex ℚ X
  let hS := relativeChainShortComplex_shortExact ℚ X
  haveI : Mono (HomologicalComplex.homologyMap S.f n) := by
    change Mono (HomologicalComplex.homologyMap ((chainPairFunctor ℚ).obj X).hom n)
    infer_instance
  haveI : Epi (HomologicalComplex.homologyMap S.f (n + 1)) := by
    change Epi (HomologicalComplex.homologyMap ((chainPairFunctor ℚ).obj X).hom (n + 1))
    infer_instance
  have hδ : hS.δ (n + 1) n (by rfl) = 0 := by
    apply (cancel_mono (HomologicalComplex.homologyMap S.f n)).mp
    rw [zero_comp]
    exact hS.δ_comp (n + 1) n (by rfl)
  have hπ : HomologicalComplex.homologyMap S.g (n + 1) = 0 := by
    apply (cancel_epi (HomologicalComplex.homologyMap S.f (n + 1))).mp
    rw [comp_zero, ← HomologicalComplex.homologyMap_comp, S.zero,
      HomologicalComplex.homologyMap_zero]
  exact (hS.homology_exact₃ (n + 1) n (by rfl)).isZero_of_both_zeros hπ hδ

/-- The actual product normal pair has zero degree-one rational homology in every positive complex rank over an arbitrary base.
Source: Hatcher, Algebraic Topology, §2.1, the relative sequence and path connectivity of punctured complex fibres. -/
theorem i1_productNormalRelativeHomologyOne_isZero {B : Type} [TopologicalSpace B]
    (k : ℕ) (hk : 0 < k) : IsZero (RelativeHomology ℚ (i1_productNormalPair B k) 1) := by
  haveI := i1_productComplementHomologyZero_isIso (B := B) k hk
  have hw : (fun _ : Fin k => (1 : ℂ)) ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h ⟨0, hk⟩)
  haveI := i1_productComplementHomology_epi (B := B) k (fun _ => 1) hw 1
  exact i1_relativeHomologySuccessor_isZero (i1_productNormalPair B k) 0

end HodgeLean.Foundations.BundleThom
