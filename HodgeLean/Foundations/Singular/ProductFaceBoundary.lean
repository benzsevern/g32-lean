import HodgeLean.Foundations.Singular.ProductFaces

/-! Boundary compatibility of the actual Alexander–Whitney bidegree components. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The front/back-face components satisfy the signed tensor boundary identity.
Source: Hatcher, Algebraic Topology, §3.2, Lemma 3.6 and the Alexander–Whitney map. -/
theorem productFaceComponent_boundary (X Y : TopCat.{0}) (p q : ℕ)
    (z : (rationalChains (TopCat.of (X × Y))).X (p + q + 1)) :
    productFaceComponent X Y p q
        (((rationalChains (TopCat.of (X × Y))).d (p + q + 1) (p + q)).hom z) =
      TensorProduct.map (((rationalChains X).d (p + 1) p).hom) LinearMap.id
        (productFaceComponent X Y (p + 1) q (reassocChain ℚ p q z)) +
      (-1 : ℚ) ^ p • TensorProduct.map LinearMap.id (((rationalChains Y).d (q + 1) q).hom)
        (productFaceComponent X Y p (q + 1) z) := by
  apply sub_eq_zero.mp
  apply tensorScalarPairings_separate
  intro φ ψ
  rw [map_sub]
  apply sub_eq_zero.mpr
  have h := congrArg (fun k => k z)
    (coboundary_cupCochain (TopCat.of (X × Y)) p q
      (cochainMap ℚ (TopCat.toSSet.map (productFirst X Y)) p φ)
      (cochainMap ℚ (TopCat.toSSet.map (productSecond X Y)) q ψ))
  have hx := HodgeLean.Foundations.Simplicial.coboundary_cochainMap
    (TopCat.toSSet.obj X) (TopCat.toSSet.map (productFirst X Y)) p φ
  have hy := HodgeLean.Foundations.Simplicial.coboundary_cochainMap
    (TopCat.toSSet.obj Y) (TopCat.toSSet.map (productSecond X Y)) q ψ
  rw [hx, hy] at h
  have hpair (i j : ℕ) (a : (rationalChains X).X i →ₗ[ℚ] ℚ)
      (b : (rationalChains Y).X j →ₗ[ℚ] ℚ)
      (u : (rationalChains (TopCat.of (X × Y))).X (i + j)) :=
    congrArg (fun k => k u) (productFaceComponent_pairing X Y i j a b)
  have hm₁ := congrArg (fun k => k
      (productFaceComponent X Y (p + 1) q (reassocChain ℚ p q z)))
    (tensorScalarPairing_map (((rationalChains X).d (p + 1) p).hom) LinearMap.id φ ψ)
  have hm₂ := congrArg (fun k => k (productFaceComponent X Y p (q + 1) z))
    (tensorScalarPairing_map LinearMap.id (((rationalChains Y).d (q + 1) q).hom) φ ψ)
  simp only [LinearMap.comp_apply, LinearMap.comp_id, LinearMap.id_comp] at hm₁ hm₂
  rw [map_add, map_smul, hm₁, hm₂]
  change _ = tensorScalarPairing (coboundary ℚ p φ) ψ
      (productFaceComponent X Y (p + 1) q (reassocChain ℚ p q z)) +
    (-1 : ℚ) ^ p • tensorScalarPairing φ (coboundary ℚ q ψ)
      (productFaceComponent X Y p (q + 1) z)
  have he₀ := hpair p q φ ψ
    (((rationalChains (TopCat.of (X × Y))).d (p + q + 1) (p + q)).hom z)
  have he₁ := hpair (p + 1) q (coboundary ℚ p φ) ψ (reassocChain ℚ p q z)
  have he₂ := hpair p (q + 1) φ (coboundary ℚ q ψ) z
  dsimp only [LinearMap.comp_apply] at he₀ he₁ he₂
  erw [he₀, he₁, he₂]
  exact h

#print axioms productFaceComponent_boundary
end HodgeLean.Foundations.Singular
