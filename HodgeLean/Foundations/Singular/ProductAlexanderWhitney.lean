import HodgeLean.Foundations.Singular.ProductFaces
import Mathlib.Data.Finset.NatAntidiagonal

/-! The specified Alexander–Whitney degree maps on actual rational singular chains. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- One bidegree summand of the actual Alexander–Whitney map.
Source: Hatcher, Algebraic Topology, §3.2, the Alexander–Whitney formula. -/
def productFaceSummand (X Y : TopCat.{0}) (n p q : ℕ) (hpq : p + q = n) :
    (rationalChains (TopCat.of (X × Y))).X n →ₗ[ℚ] (rationalTensorChains X Y).X n :=
  ((tensorChainInclusion X Y p q n hpq).hom).comp
    ((productFaceComponent X Y p q).comp
      (((rationalChains (TopCat.of (X × Y))).XIsoOfEq hpq.symm).hom.hom))

/-- The actual Alexander–Whitney degree map is the finite sum of its front/back components.
Source: Hatcher, Algebraic Topology, §3.2, the Alexander–Whitney formula. -/
def productAlexanderWhitneyDegree (X Y : TopCat.{0}) (n : ℕ) :
    (rationalChains (TopCat.of (X × Y))).X n →ₗ[ℚ] (rationalTensorChains X Y).X n :=
  ∑ pq ∈ (Finset.antidiagonal n).attach,
    productFaceSummand X Y n pq.1.1 pq.1.2 (Finset.mem_antidiagonal.mp pq.2)

/-- In degree zero the Alexander–Whitney sum has its sole vertex component.
Source: Hatcher, Algebraic Topology, §3.2, the Alexander–Whitney formula in degree zero. -/
theorem productAlexanderWhitneyDegree_zero (X Y : TopCat.{0}) :
    productAlexanderWhitneyDegree X Y 0 = productFaceSummand X Y 0 0 0 rfl := by
  unfold productAlexanderWhitneyDegree
  let a : ↥(Finset.antidiagonal 0) := ⟨(0, 0), Finset.mem_antidiagonal.mpr rfl⟩
  rw [Finset.sum_eq_single a]
  · intro b hb hba
    exfalso
    apply hba
    apply Subtype.ext
    have h := Finset.mem_antidiagonal.mp b.2
    apply Prod.ext <;> dsimp [a] <;> omega
  · intro ha
    exact (ha (Finset.mem_attach _ a)).elim

#print axioms productAlexanderWhitneyDegree_zero
#print axioms productFaceSummand
#print axioms productAlexanderWhitneyDegree
end HodgeLean.Foundations.Singular
