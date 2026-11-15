import HodgeLean.Foundations.Singular.ProductAlexanderWhitney
import HodgeLean.Foundations.Singular.ProductZero

/-! Vertex normalization of the actual front/back-face comparison. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- Projecting the paired simplex recovers its first factor.
Source: Hatcher, Algebraic Topology, §3.2, products of singular simplices. -/
theorem productFirst_pairedSimplex (X Y : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (τ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    (TopCat.toSSet.map (productFirst X Y)).app _ (pairedSimplex X Y n σ τ) = σ := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  rfl

/-- Projecting the paired simplex recovers its second factor.
Source: Hatcher, Algebraic Topology, §3.2, products of singular simplices. -/
theorem productSecond_pairedSimplex (X Y : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (τ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    (TopCat.toSSet.map (productSecond X Y)).app _ (pairedSimplex X Y n σ τ) = τ := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  rfl

/-- The degree-zero face component splits an actual product vertex into its two projections.
Source: Hatcher, Algebraic Topology, §3.2, the Alexander–Whitney formula in degree zero. -/
theorem productFaceComponent_vertex (X Y : TopCat.{0})
    (σ : (TopCat.toSSet.obj (TopCat.of (X × Y))) _⦋0⦌) :
    productFaceComponent X Y 0 0 (chainOfSimplex ℚ σ) =
      chainOfSimplex ℚ ((TopCat.toSSet.map (productFirst X Y)).app _ σ) ⊗ₜ[ℚ]
      chainOfSimplex ℚ ((TopCat.toSSet.map (productSecond X Y)).app _ σ) := by
  have hf : frontInclusion 0 0 = 𝟙 (SimplexCategory.mk 0) := by
    ext i
    rfl
  have hb : backInclusion 0 0 = 𝟙 (SimplexCategory.mk 0) := by
    ext i
    simp [backInclusion]
  rw [productFaceComponent_simplex]
  simp [frontFace, backFace, hf, hb]
  rfl

/-- Pairing the projections of a product simplex recovers that simplex.
Source: Hatcher, Algebraic Topology, §3.2, products of singular simplices. -/
theorem pairedSimplex_projections (X Y : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj (TopCat.of (X × Y))) _⦋n⦌) :
    pairedSimplex X Y n ((TopCat.toSSet.map (productFirst X Y)).app _ σ)
      ((TopCat.toSSet.map (productSecond X Y)).app _ σ) = σ := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  rfl

/-- The actual Alexander–Whitney degree-zero map sends a vertex to its two factor vertices.
Source: Hatcher, Algebraic Topology, §3.2, the Alexander–Whitney formula in degree zero. -/
theorem productAlexanderWhitneyDegree_vertex (X Y : TopCat.{0})
    (σ : (TopCat.toSSet.obj (TopCat.of (X × Y))) _⦋0⦌) :
    productAlexanderWhitneyDegree X Y 0 (chainOfSimplex ℚ σ) =
      (tensorChainInclusion X Y 0 0 0 rfl).hom
        (chainOfSimplex ℚ ((TopCat.toSSet.map (productFirst X Y)).app _ σ) ⊗ₜ[ℚ]
          chainOfSimplex ℚ ((TopCat.toSSet.map (productSecond X Y)).app _ σ)) := by
  rw [productAlexanderWhitneyDegree_zero]
  change (tensorChainInclusion X Y 0 0 0 rfl).hom
    (productFaceComponent X Y 0 0 (chainOfSimplex ℚ σ)) = _
  rw [productFaceComponent_vertex]
  rfl

#print axioms productAlexanderWhitneyDegree_vertex
#print axioms pairedSimplex_projections
#print axioms productFaceComponent_vertex
#print axioms productSecond_pairedSimplex
#print axioms productFirst_pairedSimplex
end HodgeLean.Foundations.Singular
