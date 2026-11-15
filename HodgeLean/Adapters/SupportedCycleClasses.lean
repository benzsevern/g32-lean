import HodgeLean.Adapters.SupportedCycleClassesProofs

/-!
Rational supported classes and finite weighted cycle families.
Source: Hatcher, Algebraic Topology, §3.1; Fulton, Intersection Theory, §19.1.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open scoped BigOperators
namespace HodgeLean.Adapters.SupportedCycleClasses

/-- Disjoint normalized rational cycle classes give a normalized finite weighted sum.
Source: Fulton, Intersection Theory, second edition, §19.1;
SchoenCycleC2NormalizedSumHelpers.s2e_rationalOrbitCycle_normalized_sum,
generalized from orbit components to disjoint finite cycle families.
-/
theorem normalized_sum {ι : Type*} [Fintype ι] {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] [IsSeparated q] (k : ℕ)
    (γ : ι → AlgebraicCycle Z ℚ)
    (hclosed : ∀ i, IsClosed (a3b4_cycleSupport q (γ i)))
    (hdisj : ∀ i j, i ≠ j → Disjoint
      (a3b4_cycleSupport q (γ i)) (a3b4_cycleSupport q (γ j)))
    (c : ∀ i, CohomologyWithSupport ℚ (a3b4_an q)
      (a3b4_cycleSupport q (γ i)) (2 * k))
    (hc : ∀ i, a3b4_IsCycleClass q (γ i) k (c i)) (a : ι → ℚ) :
    ∃ b : CohomologyWithSupport ℚ (a3b4_an q)
        (a3b4_cycleSupport q (∑ i, (γ i).mapRange (a i * ·) (mul_zero _))) (2 * k),
      a3b4_IsCycleClass q (∑ i, (γ i).mapRange (a i * ·) (mul_zero _)) k b ∧
      forgetSupport ℚ (a3b4_an q) (a3b4_cycleSupport q (∑ i, (γ i).mapRange (a i * ·) (mul_zero _))) (2 * k) b =
        ∑ i, a i • forgetSupport ℚ (a3b4_an q) (a3b4_cycleSupport q (γ i)) (2 * k) (c i) := normalized_sum_aux q k γ hclosed hdisj c hc a


-- A one-component coefficient-one family retains its given local normalization.
example {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (k : ℕ) (γ : AlgebraicCycle Z ℚ)
    (c : CohomologyWithSupport ℚ (a3b4_an q) (a3b4_cycleSupport q γ) (2 * k))
    (hc : a3b4_IsCycleClass q γ k c) :
    ∃ b : CohomologyWithSupport ℚ (a3b4_an q)
        (a3b4_cycleSupport q (∑ _ : Unit, γ.mapRange ((1 : ℚ) * ·) (mul_zero _))) (2 * k),
      a3b4_IsCycleClass q (∑ _ : Unit, γ.mapRange ((1 : ℚ) * ·) (mul_zero _)) k b ∧
      forgetSupport ℚ (a3b4_an q) _ (2 * k) b =
        ∑ _ : Unit, (1 : ℚ) • forgetSupport ℚ (a3b4_an q) _ (2 * k) c := by
  classical
  have hγ : (∑ _ : Unit, γ.mapRange ((1 : ℚ) * ·) (mul_zero _)) = γ := by
    ext ξ
    simp
  rw [hγ]
  simp only [one_smul, Finset.univ_unique, Finset.sum_singleton]
  exact ⟨c, hc, rfl⟩

end HodgeLean.Adapters.SupportedCycleClasses
