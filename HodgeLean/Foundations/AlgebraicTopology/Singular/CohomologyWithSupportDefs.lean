import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology

/-!
Rational supported classes and finite weighted cycle families.
Source: Hatcher, Algebraic Topology, §3.1; Fulton, Intersection Theory, §19.1.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
namespace AlgebraicTopology.Singular.SupportedClasses

/-- A finite rational sum with support inclusions required only at nonzero weights.
Source: SchoenCycleC2SupportedSumHelpers.s2e_weightedSupportedClass.
-/
def weightedSum {ι : Type*} [Fintype ι] (X : TopCat.{0}) (n : ℕ)
    (S : ι → Set X) (T : Set X) (a : ι → ℚ)
    (hST : ∀ i, a i ≠ 0 → S i ⊆ T)
    (c : ∀ i, CohomologyWithSupport ℚ X (S i) n) :
    CohomologyWithSupport ℚ X T n := by
  classical
  exact ∑ i, if h : a i ≠ 0 then
    a i • enlargeSupport ℚ X (hST i h) n (c i) else 0

example (X : TopCat.{0}) (S : Set X) (n : ℕ)
    (c : CohomologyWithSupport ℚ X S n) :
    weightedSum X n (fun _ : Unit => S) S (fun _ => 1) (fun _ _ => Set.Subset.rfl)
      (fun _ => c) = c := by
  classical
  simp only [weightedSum, ne_eq, one_ne_zero, not_false_eq_true, dite_true,
    one_smul, Finset.univ_unique, Finset.sum_singleton, enlargeSupport_rfl,
    LinearMap.id_apply]

end AlgebraicTopology.Singular.SupportedClasses
