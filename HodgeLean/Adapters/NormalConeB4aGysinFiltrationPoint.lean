import HodgeLean.Adapters.NormalConeB4aGysinLowerStrata

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- Every point of a closed support occurs in one actual smooth layer of its
canonical descending closed filtration. -/
theorem a3b4a_gysin_point_mem_smooth_filtration_layer
    {Z : Scheme.{0}} [IsNoetherian Z]
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    (S : Closeds Z) (z : Z) (hz : z ∈ S) :
    ∃ k : ℕ, z ∈ reducedSmoothClosedFiltration q S k ∧
      z ∉ reducedSmoothClosedFiltration q S (k + 1) := by
  revert hz
  induction S using (wellFounded_lt (α := Closeds Z)).induction with
  | h S ih =>
    intro hz
    by_cases hzR : z ∈ reducedClosedSingularRemainder q S
    · have hS : S ≠ ⊥ := by
        intro he
        have hz' : z ∈ ((⊥ : Closeds Z) : Set Z) := he ▸ hz
        rw [Closeds.coe_bot] at hz'
        exact hz'
      obtain ⟨k, hk, hknext⟩ := ih _ (reducedClosedSingularRemainder_lt q S hS) hzR
      refine ⟨k + 1, ?_, ?_⟩
      · simpa only [reducedSmoothClosedFiltration_succ_start] using hk
      · simpa only [reducedSmoothClosedFiltration_succ_start] using hknext
    · exact ⟨0, hz, hzR⟩

end HodgeLean.Adapters
