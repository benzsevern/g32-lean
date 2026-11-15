import HodgeLean.Foundations.Program.SchoenTransferQ3SliceDetection

/-! Supported pair maps constructed from the actual normal-slice inclusion. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The actual inclusion of a normal slice, on specified neighbourhoods,
defines a map of support-complement pairs by its normal-coordinate equation. -/
def s4_q3_slice_neighbourhood_pair_map
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {c : ℕ}
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
    (d : OpenPartialHomeomorph N (F × (Fin c → ℂ)))
    (S : Set M) (T : Set N)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hT : ∀ y ∈ d.source, y ∈ T ↔ (d y).2 = 0)
    (j : C(N, M)) (V : Set N) (W : Set M)
    (hV : V ⊆ d.source) (hW : W ⊆ e.source)
    (hj : ∀ y ∈ V, j y ∈ W)
    (hnormal : ∀ y ∈ V, (e (j y)).2 = (d y).2) :
    neighborhoodSupportComplementPair V T ⟶ neighborhoodSupportComplementPair W S :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun y : V => ⟨j y.1, hj y.1 y.2⟩,
      (j.continuous.comp continuous_subtype_val).subtype_mk _⟩)
    (by
      intro y hy hSjy
      apply hy
      apply (hT y.1 (hV y.2)).mpr
      rw [← hnormal y.1 y.2]
      exact (hS (j y.1) (hW (hj y.1 y.2))).mp hSjy)

/-- The constructed slice pair map pulls back the ambient normal coclass
to the slice normal coclass with its exact ordered complex normalization. -/
theorem s4_q3_slice_neighbourhood_pair_map_normal_coclass
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
    (d : OpenPartialHomeomorph N (F × (Fin c → ℂ)))
    (S : Set M) (T : Set N)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hT : ∀ y ∈ d.source, y ∈ T ↔ (d y).2 = 0)
    (j : C(N, M)) (V : Set N) (W : Set M)
    (hV : V ⊆ d.source) (hW : W ⊆ e.source)
    (hj : ∀ y ∈ V, j y ∈ W)
    (hnormal : ∀ y ∈ V, (e (j y)).2 = (d y).2) :
    relativeCohomologyMap ℚ (2 * c)
      (s4_q3_slice_neighbourhood_pair_map e d S T hS hT j V W hV hW hj hnormal)
      (chartNormalProjectionCoclass E c e S hS W hW) =
        chartNormalProjectionCoclass F c d T hT V hV := by
  apply s4_q3_normal_coclass_pullback F E c d e T S hT hS V W hV hW
  intro y
  exact hnormal y.1 y.2

end HodgeLean.Foundations.Program
