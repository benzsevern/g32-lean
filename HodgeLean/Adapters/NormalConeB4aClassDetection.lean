import HodgeLean.Adapters.NormalConeB4aClassGlobal
import HodgeLean.Adapters.NormalConeB4aClassRestriction

/-! # Detecting supported classes from their local restrictions -/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace

/-- Restriction to the whole ambient space, represented as a subtype, is injective. -/
theorem a3b4a_classLocal_restrict_univ_injective
    {M : Type} [TopologicalSpace M] (S : Set M) (n : ℕ) :
    Function.Injective (relativeCohomologyMap ℚ n
      (a3b4_neighborhoodPairMap (Set.univ : Set M) S)) := by
  let g : TopPair.ofSubset (X := TopCat.of M) Sᶜ ⟶
      neighborhoodSupportComplementPair (Set.univ : Set M) S :=
    TopPair.ofHom (TopCat.ofHom ⟨fun x => ⟨x, Set.mem_univ x⟩, by fun_prop⟩)
      (TopCat.ofHom ⟨fun x => ⟨⟨x.1, Set.mem_univ x.1⟩, x.2⟩, by fun_prop⟩)
      (by ext; rfl)
  have hg : g ≫ a3b4_neighborhoodPairMap (Set.univ : Set M) S = 𝟙 _ := rfl
  intro α β h
  have hh := congrArg (relativeCohomologyMap ℚ n g) h
  simpa only [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    hg, relativeCohomologyMap_id, LinearMap.id_apply] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In the lowest normal degree, a class on a flattened closed support is zero
if it restricts to zero near every point of the support. -/
theorem a3b4a_classRelative_eq_zero_of_locally_zero
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (S : Closeds X) (c : ℕ)
    (hcharts : ∀ x ∈ S, ∃ (r d : ℕ)
      (e : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin d → ℂ))),
      c ≤ d ∧ x ∈ e.source ∧ ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (α : RelativeCohomology ℚ (TopPair.ofSubset (X := X) (S : Set X)ᶜ) (2 * c))
    (hα : ∀ x ∈ S, ∃ U : Opens X, x ∈ U ∧
      relativeCohomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap (M := X) (U : Set X) (S : Set X)) α = 0) :
    α = 0 := by
  have hH (j : ℕ) (hj : j < 2 * c) : IsZero
      (((⊤ : Opens X).isOpenEmbedding.sheafPullback AddCommGrpCat).obj
        (supportRelativeCohomologySheaf X S j)) :=
    ((⊤ : Opens X).isOpenEmbedding.sheafPullback AddCommGrpCat).map_isZero
      (a3b4a_classSheaf_vanishing_of_flatteningCharts X S S.isClosed c hcharts j hj)
  apply a3b4a_classLocal_restrict_univ_injective (S : Set X) (2 * c)
  rw [map_zero]
  apply ccm5_relativeGerms_injective_of_lowerVanishing X S ⊤ (2 * c) hH
  funext x
  dsimp only
  have hzero : supportRelativeCohomologyGerm X S (2 * c) ⊤ x.1 x.2 0 = 0 := by
    simp only [supportRelativeCohomologyGerm, map_zero]
  rw [hzero]
  by_cases hxS : x.1 ∈ S
  · obtain ⟨U, hxU, hU⟩ := hα x.1 hxS
    rw [← supportRelativeCohomologyGerm_restrict X S (2 * c)
      (show U ≤ ⊤ from le_top) x.1 hxU]
    have hr := (a3b4a_classLocal_restriction_comp (S : Set X)
      (show (U : Set X) ⊆ Set.univ from Set.subset_univ _) (2 * c) α).trans hU
    exact (congrArg (supportRelativeCohomologyGerm X S (2 * c) U x.1 hxU) hr).trans
      (by simp only [supportRelativeCohomologyGerm, map_zero])
  · exact supportRelativeCohomologyGerm_eq_zero_of_not_mem X S (2 * c)
      S.isClosed ⊤ x.1 x.2 hxS _

/-- Restriction to the ambient space as its universal subtype is bijective. -/
theorem a3b4a_classLocal_restrict_univ_bijective
    {M : Type} [TopologicalSpace M] (S : Set M) (n : ℕ) :
    Function.Bijective (relativeCohomologyMap ℚ n
      (a3b4_neighborhoodPairMap (Set.univ : Set M) S)) := by
  refine ⟨a3b4a_classLocal_restrict_univ_injective S n, ?_⟩
  let g : TopPair.ofSubset (X := TopCat.of M) Sᶜ ⟶
      neighborhoodSupportComplementPair (Set.univ : Set M) S :=
    TopPair.ofHom (TopCat.ofHom ⟨fun x => ⟨x, Set.mem_univ x⟩, by fun_prop⟩)
      (TopCat.ofHom ⟨fun x => ⟨⟨x.1, Set.mem_univ x.1⟩, x.2⟩, by fun_prop⟩)
      (by ext; rfl)
  have hg : a3b4_neighborhoodPairMap (Set.univ : Set M) S ≫ g = 𝟙 _ := rfl
  intro α
  refine ⟨relativeCohomologyMap ℚ n g α, ?_⟩
  simp only [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    hg, relativeCohomologyMap_id, LinearMap.id_apply]

end HodgeLean.Adapters
