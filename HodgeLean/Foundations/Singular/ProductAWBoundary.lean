import HodgeLean.Foundations.Singular.ProductAWComponents
import HodgeLean.Foundations.Singular.ProductFaceBoundary
import HodgeLean.Foundations.Singular.ProductProjectionBoundary
import HodgeLean.Foundations.Singular.RationalSigns

/-! The boundary identity for the actual finite Alexander–Whitney map. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The actual finite Alexander–Whitney degree maps commute with the boundary.
Source: Hatcher, Algebraic Topology, §3.2, the Alexander–Whitney chain map. -/
theorem productAlexanderWhitneyDegree_boundary (X Y : TopCat.{0}) (n : ℕ) :
    (rationalChains (TopCat.of (X × Y))).d (n + 1) n ≫
        ModuleCat.ofHom (productAlexanderWhitneyDegree X Y n) =
      ModuleCat.ofHom (productAlexanderWhitneyDegree X Y (n + 1)) ≫
        (rationalTensorChains X Y).d (n + 1) n := by
  apply tensorChainProjection_jointly_monic X Y n
  intro p q hpq
  subst n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have h₀ := congrArg (fun k => k
      (((rationalChains (TopCat.of (X × Y))).d (p + q + 1) (p + q)).hom z))
    (productAlexanderWhitneyDegree_projection_sum X Y p q)
  have h₁ := congrArg (fun k => k z)
    (productAlexanderWhitneyDegree_projection X Y (p + q + 1) (p + 1) q (by omega))
  have h₂ := congrArg (fun k => k z)
    (productAlexanderWhitneyDegree_projection_sum X Y p (q + 1))
  change (tensorChainProjection X Y p q (p + q)).hom
      (productAlexanderWhitneyDegree X Y (p + q)
        (((rationalChains (TopCat.of (X × Y))).d (p + q + 1) (p + q)).hom z)) =
    productFaceComponent X Y p q
      (((rationalChains (TopCat.of (X × Y))).d (p + q + 1) (p + q)).hom z) at h₀
  change (tensorChainProjection X Y (p + 1) q (p + q + 1)).hom
      (productAlexanderWhitneyDegree X Y (p + q + 1) z) =
    productFaceComponent X Y (p + 1) q (reassocChain ℚ p q z) at h₁
  change (tensorChainProjection X Y p (q + 1) (p + q + 1)).hom
      (productAlexanderWhitneyDegree X Y (p + q + 1) z) =
    productFaceComponent X Y p (q + 1) z at h₂
  have hb := congrArg (fun k => ModuleCat.Hom.hom k
      (productAlexanderWhitneyDegree X Y (p + q + 1) z))
    (tensorChain_boundary_projection X Y p q)
  change (tensorChainProjection X Y p q (p + q)).hom
      (((rationalTensorChains X Y).d (p + q + 1) (p + q)).hom
        (productAlexanderWhitneyDegree X Y (p + q + 1) z)) =
    TensorProduct.map (((rationalChains X).d (p + 1) p).hom) LinearMap.id
      ((tensorChainProjection X Y (p + 1) q (p + q + 1)).hom
        (productAlexanderWhitneyDegree X Y (p + q + 1) z)) +
    ((((-1 : ℤˣ) ^ p) •
      (tensorChainProjection X Y p (q + 1) (p + q + 1) ≫
        ((rationalChains X).X p ◁ (rationalChains Y).d (q + 1) q))).hom
      (productAlexanderWhitneyDegree X Y (p + q + 1) z)) at hb
  rw [rational_sign_apply] at hb
  change _ = TensorProduct.map (((rationalChains X).d (p + 1) p).hom) LinearMap.id
      ((tensorChainProjection X Y (p + 1) q (p + q + 1)).hom
        (productAlexanderWhitneyDegree X Y (p + q + 1) z)) +
    (-1 : ℚ) ^ p • TensorProduct.map LinearMap.id (((rationalChains Y).d (q + 1) q).hom)
      ((tensorChainProjection X Y p (q + 1) (p + q + 1)).hom
        (productAlexanderWhitneyDegree X Y (p + q + 1) z)) at hb
  rw [h₁, h₂] at hb
  change (tensorChainProjection X Y p q (p + q)).hom
      (productAlexanderWhitneyDegree X Y (p + q)
        (((rationalChains (TopCat.of (X × Y))).d (p + q + 1) (p + q)).hom z)) =
    (tensorChainProjection X Y p q (p + q)).hom
      (((rationalTensorChains X Y).d (p + q + 1) (p + q)).hom
        (productAlexanderWhitneyDegree X Y (p + q + 1) z))
  exact h₀.trans ((productFaceComponent_boundary X Y p q z).trans hb.symm)

#print axioms productAlexanderWhitneyDegree_boundary
end HodgeLean.Foundations.Singular
