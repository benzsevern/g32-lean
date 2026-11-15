import HodgeLean.Foundations.Singular.ProductAugmentation

/-! The first extension of the actual tensor-to-product chain comparison. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The actual first-degree model obstruction has a singular-chain filler.
Source: Hatcher, Algebraic Topology, §3.2, the augmented acyclic-models construction. -/
theorem productModel_first_filler (p q : ℕ) (hpq : p + q = 1) :
    ∃ w : (rationalChains (TopCat.of (simplexProductModel p q))).X 1,
      ((rationalChains (TopCat.of (simplexProductModel p q))).d 1 0).hom w =
        tensorProductZero
          (TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1))))
          (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))
          (((rationalTensorChains
            (TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1))))
            (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).d 1 0).hom
              (universalTensorSimplex p q 1 hpq)) := by
  letI := simplexProductModel_contractible p q
  refine contractible_zero_cycle_filler_of_point_map (simplexProductModel p q) _ ?_
  exact tensorProductZero_point_boundary _ _ (universalTensorSimplex p q 1 hpq)

/-- The actual degree-zero cross product extends naturally through degree one.
Source: Hatcher, Algebraic Topology, §3.2, the augmented acyclic-models construction. -/
theorem tensorProduct_first_degree_exists :
    ∃ a : ∀ X Y : TopCat.{0}, (rationalTensorChains X Y).X 1 →ₗ[ℚ]
        (rationalChains (TopCat.of (X × Y))).X 1,
      (∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
        (a X' Y').comp ((rationalTensorChainMap f g).f 1).hom =
          (((rationalChainMap (topologicalProductMap f g)).f 1).hom).comp (a X Y)) ∧
      (∀ X Y : TopCat.{0},
        (((rationalChains (TopCat.of (X × Y))).d 1 0).hom).comp (a X Y) =
          (tensorProductZero X Y).comp ((rationalTensorChains X Y).d 1 0).hom) := by
  let c (p q : ℕ) (hpq : p + q = 1) := Classical.choose (productModel_first_filler p q hpq)
  have hc (p q : ℕ) (hpq : p + q = 1) := Classical.choose_spec (productModel_first_filler p q hpq)
  refine ⟨fun X Y => productModelExtension X Y 1 c, ?_, ?_⟩
  · intro X X' Y Y' f g
    exact productModelExtension_naturality f g 1 c
  · intro X Y
    exact productModelExtension_boundary 0 tensorProductZero
      (fun f g => tensorProductZero_naturality f g) c hc X Y

#print axioms tensorProduct_first_degree_exists
#print axioms productModel_first_filler
end HodgeLean.Foundations.Singular
