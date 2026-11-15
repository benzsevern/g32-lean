import Mathlib.RepresentationTheory.Invariants
import Mathlib.CategoryTheory.Abelian.Exact

/-! Exactness of rational fixed vectors for finite groups. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

variable (G : Type) [Group G] [Fintype G]

lemma rational_invariants_preserves_epimorphisms :
    (Rep.invariantsFunctor ℚ G).PreservesEpimorphisms := by
  letI : Invertible (Fintype.card G : ℚ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  refine ⟨?_⟩
  intro X Y f hf
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro y
  obtain ⟨x, hx⟩ := (Rep.epi_iff_surjective f).mp hf y.1
  refine ⟨⟨X.ρ.averageMap x, X.ρ.averageMap_invariant x⟩, ?_⟩
  apply Subtype.ext
  change f.hom (X.ρ.averageMap x) = y.1
  have hcomm : f.hom (X.ρ.averageMap x) = Y.ρ.averageMap (f.hom x) := by
    simp only [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum,
      Representation.asAlgebraHom_of, LinearMap.smul_apply, LinearMap.sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    exact Rep.hom_comm_apply f g x
  rw [hcomm, hx, Representation.averageMap_id _ _ y.2]

lemma rational_invariants_preserves_homology :
    CategoryTheory.Functor.PreservesHomology (Rep.invariantsFunctor ℚ G) := by
  letI := rational_invariants_preserves_epimorphisms G
  exact CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels _

end HodgeLean.Foundations.QuotientDuality
