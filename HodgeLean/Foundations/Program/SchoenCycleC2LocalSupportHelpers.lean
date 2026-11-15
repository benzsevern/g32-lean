import HodgeLean.Foundations.AlgebraicTopology.Singular.CohomologyWithSupport
import HodgeLean.Adapters.NormalConeB4aClassRestriction
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.RelativeCohomologySheaf

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The identity on a neighbourhood as a map from larger to smaller allowed support. -/
def s2e_localSupportMap {M : Type} [TopologicalSpace M] (V S T : Set M)
    (h : ∀ x ∈ V, x ∈ S → x ∈ T) :
    neighborhoodSupportComplementPair V T ⟶ neighborhoodSupportComplementPair V S :=
  TopPair.ofHom (𝟙 (TopCat.of V))
    (TopCat.ofHom ⟨fun x => ⟨x.1, fun hx => x.2 (h x.1.1 x.1.2 hx)⟩, by fun_prop⟩)
    (by ext x; rfl)

/-- Restriction of an enlarged class is the enlargement of its neighbourhood restriction. -/
theorem s2e_enlargeSupport_restrict {M : Type} [TopologicalSpace M]
    (V S T : Set M) (hST : S ⊆ T) (n : ℕ)
    (c : CohomologyWithSupport ℚ (TopCat.of M) S n) :
    relativeCohomologyMap ℚ n (HodgeLean.Adapters.a3b4_neighborhoodPairMap V T)
      (enlargeSupport ℚ (TopCat.of M) hST n c) =
    relativeCohomologyMap ℚ n (s2e_localSupportMap V S T (fun x _ hx => hST hx))
      (relativeCohomologyMap ℚ n (HodgeLean.Adapters.a3b4_neighborhoodPairMap V S) c) := by
  exact SupportedClasses.pullback_enlarge
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of V ⟶ TopCat.of M) hST n c

/-- Normal projection coclasses respect a change of allowed support and charts
that have equal coordinate values on the neighbourhood. -/
theorem s2e_localSupportMap_normalCoclass
    {M : Type} [TopologicalSpace M] (r k : ℕ) (V S T : Set M)
    (h : ∀ x ∈ V, x ∈ S → x ∈ T)
    (e f : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin k → ℂ)))
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hT : ∀ y ∈ f.source, y ∈ T ↔ (f y).2 = 0)
    (hVe : V ⊆ e.source) (hVf : V ⊆ f.source)
    (hef : ∀ x ∈ V, e x = f x) :
    relativeCohomologyMap ℚ (2 * k) (s2e_localSupportMap V S T h)
      (chartNormalProjectionCoclass (Fin r → ℂ) k e S hS V hVe) =
      chartNormalProjectionCoclass (Fin r → ℂ) k f T hT V hVf := by
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  congr 1
  congr 1
  apply MorphismProperty.Arrow.Hom.ext
  · ext x
    apply Subtype.ext
    exact congrArg Prod.snd (hef x.1.1 x.1.2)
  · ext x
    exact congrArg Prod.snd (hef x.1 x.2)

/-- An enlarged class restricts to zero on any neighbourhood missing its original support. -/
theorem s2e_enlargeSupport_restrict_zero {M : Type} [TopologicalSpace M]
    (V S T : Set M) (hST : S ⊆ T) (n : ℕ)
    (hV : ∀ x ∈ V, x ∉ S) (c : CohomologyWithSupport ℚ (TopCat.of M) S n) :
    relativeCohomologyMap ℚ n (HodgeLean.Adapters.a3b4_neighborhoodPairMap V T)
      (enlargeSupport ℚ (TopCat.of M) hST n c) = 0 := by
  rw [s2e_enlargeSupport_restrict]
  letI := neighborhoodSupportRelativeCohomology_subsingleton (TopCat.of M) S n V hV
  have hz : relativeCohomologyMap ℚ n
      (HodgeLean.Adapters.a3b4_neighborhoodPairMap V S) c = 0 := Subsingleton.elim _ _
  rw [hz, map_zero]

end HodgeLean.Foundations.Program
