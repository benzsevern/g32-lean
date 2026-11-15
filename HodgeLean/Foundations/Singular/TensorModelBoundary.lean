import HodgeLean.Foundations.Singular.TensorModelExtensions
import HodgeLean.Foundations.Singular.ProductSteps

/-! Boundary control for natural extensions from actual tensor models. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- Model fillers extend to a natural primitive of the specified actual tensor map.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction of chain homotopies. -/
theorem tensorModelExtension_boundary (n m : ℕ)
    (a : ∀ X Y : TopCat.{0}, (rationalTensorChains X Y).X n →ₗ[ℚ]
      (rationalTensorChains X Y).X m)
    (ha : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      (a X' Y').comp ((rationalTensorChainMap f g).f n).hom =
        (((rationalTensorChainMap f g).f m).hom).comp (a X Y))
    (c : ∀ (p q : ℕ), p + q = n →
      (rationalTensorChains (TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1))))
        (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).X (m + 1))
    (hc : ∀ (p q : ℕ) (hpq : p + q = n),
      let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1)))
      let Y := TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1)))
      ((rationalTensorChains X Y).d (m + 1) m).hom (c p q hpq) =
        a X Y (universalTensorSimplex p q n hpq)) (X Y : TopCat.{0}) :
    (((rationalTensorChains X Y).d (m + 1) m).hom).comp
      (tensorModelExtension X Y n (m + 1) c) = a X Y := by
  apply rationalTotalTensor_linearMap_ext X Y n
  intro p q hpq σ τ
  erw [LinearMap.comp_apply, tensorModelExtension_simplex,
    rationalTensorChainMap_boundary, hc p q hpq]
  let f := singularSimplexTopCatMap X p σ
  let g := singularSimplexTopCatMap Y q τ
  let u := universalTensorSimplex p q n hpq
  have hn := LinearMap.congr_fun (ha f g) u
  change ((rationalTensorChainMap f g).f m).hom (a _ _ u) = _
  exact hn.symm.trans (congrArg (a X Y) (universalTensorSimplex_map X Y p q n hpq σ τ))

#print axioms tensorModelExtension_boundary
end HodgeLean.Foundations.Singular
