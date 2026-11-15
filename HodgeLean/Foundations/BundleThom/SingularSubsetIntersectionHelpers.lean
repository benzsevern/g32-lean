import HodgeLean.Foundations.BundleThom.RelativeSubcomplexSequenceHelpers
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.CoverSmall

/-! # Actual singular subcomplexes of topological subset intersections

The subcomplex consists of the actual singular simplices factoring through the supplied subset.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- The actual singular subcomplex supplied by inclusion of a topological subset.
Source: Hatcher, Algebraic Topology, §2.1 and §2.2, small singular chains. -/
def i1_singularSubsetRange (X : TopCat) (U : Set X) : (TopCat.toSSet.obj X).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X U))

/-- An actual singular simplex factors through a subset exactly when every one of its points lies there.
Source: Hatcher, Algebraic Topology, §2.1, singular simplices in subspaces. -/
theorem i1_mem_singularSubsetRange_iff (X : TopCat) (U : Set X)
    {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (i1_singularSubsetRange X U).obj n ↔ ∀ t, X.toSSetObjEquiv n σ t ∈ U := by
  change (∃ τ, (TopCat.toSSet.map (topologicalSubsetInclusion X U)).app n τ = σ) ↔ _
  constructor
  · rintro ⟨τ, rfl⟩ t
    change (((TopCat.of U).toSSetObjEquiv n τ) t).1 ∈ U
    exact (((TopCat.of U).toSSetObjEquiv n τ) t).2
  · intro hσ
    let τ := ((TopCat.of U).toSSetObjEquiv n).symm
      ⟨fun t => ⟨X.toSSetObjEquiv n σ t, hσ t⟩,
        (X.toSSetObjEquiv n σ).continuous.subtype_mk _⟩
    exact ⟨τ, rfl⟩

/-- Actual subset intersections give intersections of their singular subcomplexes.
Source: Hatcher, Algebraic Topology, §2.2, intersection chains in Mayer–Vietoris. -/
theorem i1_singularSubsetRange_inter (X : TopCat) (U V : Set X) :
    i1_singularSubsetRange X (U ∩ V) = i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V := by
  ext n σ
  change σ ∈ (i1_singularSubsetRange X (U ∩ V)).obj n ↔
    (σ ∈ (i1_singularSubsetRange X U).obj n ∧ σ ∈ (i1_singularSubsetRange X V).obj n)
  simp only [i1_mem_singularSubsetRange_iff, Set.mem_inter_iff]
  exact forall_and

end HodgeLean.Foundations.BundleThom
