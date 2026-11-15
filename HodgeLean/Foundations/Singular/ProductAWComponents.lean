import HodgeLean.Foundations.Singular.ProductAlexanderWhitney
import HodgeLean.Foundations.Singular.ProductProjections

/-! Bidegree components of the specified Alexander–Whitney sum. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- Projecting an Alexander–Whitney summand to its own bidegree recovers its face map.
Source: Hatcher, Algebraic Topology, §3.2, the Alexander–Whitney formula. -/
theorem productFaceSummand_projection_self (X Y : TopCat.{0}) (n p q : ℕ)
    (hpq : p + q = n) :
    (tensorChainProjection X Y p q n).hom.comp (productFaceSummand X Y n p q hpq) =
      (productFaceComponent X Y p q).comp
        (((rationalChains (TopCat.of (X × Y))).XIsoOfEq hpq.symm).hom.hom) := by
  have he := congrArg ModuleCat.Hom.hom
    (tensorChainInclusion_projection_self X Y p q n hpq)
  change (tensorChainProjection X Y p q n).hom.comp
    (tensorChainInclusion X Y p q n hpq).hom = LinearMap.id at he
  unfold productFaceSummand
  rw [← LinearMap.comp_assoc, he, LinearMap.id_comp]

/-- Projecting an Alexander–Whitney summand to a distinct bidegree gives zero.
Source: Hatcher, Algebraic Topology, §3.2, the Alexander–Whitney formula. -/
theorem productFaceSummand_projection_other (X Y : TopCat.{0}) (n p q r s : ℕ)
    (hrs : r + s = n) (h : ¬ (r = p ∧ s = q)) :
    (tensorChainProjection X Y p q n).hom.comp (productFaceSummand X Y n r s hrs) = 0 := by
  have he := congrArg ModuleCat.Hom.hom
    (tensorChainInclusion_projection_other X Y p q r s n hrs h)
  change (tensorChainProjection X Y p q n).hom.comp
    (tensorChainInclusion X Y r s n hrs).hom = 0 at he
  unfold productFaceSummand
  rw [← LinearMap.comp_assoc, he, LinearMap.zero_comp]

/-- Each projection of the finite Alexander–Whitney sum is its specified face component.
Source: Hatcher, Algebraic Topology, §3.2, the Alexander–Whitney formula. -/
theorem productAlexanderWhitneyDegree_projection (X Y : TopCat.{0}) (n p q : ℕ)
    (hpq : p + q = n) :
    (tensorChainProjection X Y p q n).hom.comp (productAlexanderWhitneyDegree X Y n) =
      (productFaceComponent X Y p q).comp
        (((rationalChains (TopCat.of (X × Y))).XIsoOfEq hpq.symm).hom.hom) := by
  unfold productAlexanderWhitneyDegree
  have hsum : (tensorChainProjection X Y p q n).hom.comp
      (∑ pq ∈ (Finset.antidiagonal n).attach,
        productFaceSummand X Y n pq.1.1 pq.1.2 (Finset.mem_antidiagonal.mp pq.2)) =
      ∑ pq ∈ (Finset.antidiagonal n).attach,
        (tensorChainProjection X Y p q n).hom.comp
          (productFaceSummand X Y n pq.1.1 pq.1.2 (Finset.mem_antidiagonal.mp pq.2)) := by
    ext z
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [hsum]
  let a : ↥(Finset.antidiagonal n) := ⟨(p, q), Finset.mem_antidiagonal.mpr hpq⟩
  rw [Finset.sum_eq_single a]
  · exact productFaceSummand_projection_self X Y n p q hpq
  · intro b hb hba
    apply productFaceSummand_projection_other
    rintro ⟨hr, hs⟩
    apply hba
    apply Subtype.ext
    exact Prod.ext hr hs
  · intro ha
    exact (ha (Finset.mem_attach _ a)).elim

/-- In its native total degree the projected Alexander–Whitney map is exactly the face component.
Source: Hatcher, Algebraic Topology, §3.2, the Alexander–Whitney formula. -/
theorem productAlexanderWhitneyDegree_projection_sum (X Y : TopCat.{0}) (p q : ℕ) :
    (tensorChainProjection X Y p q (p + q)).hom.comp
        (productAlexanderWhitneyDegree X Y (p + q)) = productFaceComponent X Y p q := by
  have h := productAlexanderWhitneyDegree_projection X Y (p + q) p q rfl
  change _ = (productFaceComponent X Y p q).comp LinearMap.id at h
  simpa only [LinearMap.comp_id] using h

#print axioms productAlexanderWhitneyDegree_projection_sum
#print axioms productAlexanderWhitneyDegree_projection
#print axioms productFaceSummand_projection_other
#print axioms productFaceSummand_projection_self
end HodgeLean.Foundations.Singular
