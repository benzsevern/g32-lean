import HodgeLean.Foundations.Singular.ProductLifts
import Mathlib.Data.Finset.NatAntidiagonal

/-! The actual bidegree projections of the rational tensor chain complex. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- Projection from the total tensor chain group to a specified bidegree.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum tensor complex. -/
def tensorChainProjection (X Y : TopCat.{0}) (p q n : ℕ) :
    (rationalTensorChains X Y).X n ⟶
      ModuleCat.of ℚ ((rationalChains X).X p ⊗[ℚ] (rationalChains Y).X q) :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := rationalChains X) (K₂ := rationalChains Y)
    (F := curriedTensor (ModuleCat ℚ)) (c := ComplexShape.down ℕ)
    (fun r s _ => if h : r = p ∧ s = q then by
      rcases h with ⟨rfl, rfl⟩
      exact 𝟙 _
    else 0)

/-- Inclusion followed by its own bidegree projection is the identity.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum tensor complex. -/
theorem tensorChainInclusion_projection_self (X Y : TopCat.{0}) (p q n : ℕ)
    (hpq : p + q = n) :
    tensorChainInclusion X Y p q n hpq ≫ tensorChainProjection X Y p q n = 𝟙 _ := by
  unfold tensorChainProjection
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp

/-- Distinct tensor bidegrees have zero projection composite.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum tensor complex. -/
theorem tensorChainInclusion_projection_other (X Y : TopCat.{0})
    (p q r s n : ℕ) (hrs : r + s = n) (h : ¬ (r = p ∧ s = q)) :
    tensorChainInclusion X Y r s n hrs ≫ tensorChainProjection X Y p q n = 0 := by
  unfold tensorChainProjection
  rw [HomologicalComplex.ι_mapBifunctorDesc, dif_neg h]

/-- The finite sum of tensor bidegree projection-inclusion composites is the identity.
Source: Hatcher, Algebraic Topology, §3.2, the direct-sum tensor complex. -/
theorem tensorChain_sum_projection (X Y : TopCat.{0}) (n : ℕ) :
    (∑ pq ∈ (Finset.antidiagonal n).attach,
      tensorChainProjection X Y pq.1.1 pq.1.2 n ≫
        tensorChainInclusion X Y pq.1.1 pq.1.2 n (Finset.mem_antidiagonal.mp pq.2)) =
      𝟙 ((rationalTensorChains X Y).X n) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro r s hrs
  change r + s = n at hrs
  change tensorChainInclusion X Y r s n hrs ≫ _ = _
  rw [Preadditive.comp_sum]
  let a : ↥(Finset.antidiagonal n) := ⟨(r, s), Finset.mem_antidiagonal.mpr hrs⟩
  rw [Finset.sum_eq_single a]
  · rw [← Category.assoc, tensorChainInclusion_projection_self]
    simp only [Category.id_comp, Category.comp_id]
    rfl
  · intro b hb hba
    have hne : ¬ (r = b.1.1 ∧ s = b.1.2) := by
      rintro ⟨hr, hs⟩
      apply hba
      apply Subtype.ext
      exact (Prod.ext hr hs).symm
    rw [← Category.assoc, tensorChainInclusion_projection_other X Y _ _ _ _ _ hrs hne,
      zero_comp]
  · intro ha
    exact (ha (Finset.mem_attach _ a)).elim

/-- Bidegree projections detect equality of maps into a total tensor chain degree.
Source: Hatcher, Algebraic Topology, §3.2, the finite direct-sum tensor complex. -/
theorem tensorChainProjection_jointly_monic (X Y : TopCat.{0}) (n : ℕ)
    {A : ModuleCat ℚ} (f g : A ⟶ (rationalTensorChains X Y).X n)
    (h : ∀ p q : ℕ, p + q = n →
      f ≫ tensorChainProjection X Y p q n = g ≫ tensorChainProjection X Y p q n) :
    f = g := by
  have hf := congrArg (fun k => f ≫ k) (tensorChain_sum_projection X Y n)
  have hg := congrArg (fun k => g ≫ k) (tensorChain_sum_projection X Y n)
  simp only [Preadditive.comp_sum, ← Category.assoc, Category.comp_id] at hf hg
  rw [← hf, ← hg]
  apply Finset.sum_congr rfl
  intro pq hpq
  rw [h pq.1.1 pq.1.2 (Finset.mem_antidiagonal.mp pq.2)]

#print axioms tensorChainProjection_jointly_monic
#print axioms tensorChain_sum_projection
#print axioms tensorChainInclusion_projection_other
#print axioms tensorChainProjection
#print axioms tensorChainInclusion_projection_self
end HodgeLean.Foundations.Singular
