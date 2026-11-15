import HodgeLean.Foundations.IntegralHomology.StageTwo.FaceComplex
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-! Reindexing geometric faces by a finite ordered set of vertices.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

variable {E : Type} [DecidableEq E] [AddCommGroup E] [Module ℝ E]

def indexedFaces {n : ℕ} (K : Geometry.SimplicialComplex ℝ E)
    (v : Fin (n + 1) → E) : PreAbstractSimplicialComplex (Fin (n + 1)) where
  faces := {s | s.image v ∈ K.faces}
  isRelLowerSet_faces := by
    classical
    intro s hs
    refine ⟨Finset.image_nonempty.mp (K.nonempty_of_mem_faces hs), ?_⟩
    intro t hts ht
    exact K.down_closed hs (Finset.image_subset_image hts) (Finset.image_nonempty.mpr ht)

theorem indexedFaces_image_contains {n : ℕ} (K : Geometry.SimplicialComplex ℝ E)
    (v : Fin (n + 1) → E) (hV : K.vertices ⊆ Set.range v)
    (s : Finset E) (hs : s ∈ K.faces) :
    ∃ t : Finset (Fin (n + 1)), t.image v = s := by
  classical
  have hsub : s ⊆ Finset.univ.image v := by
    intro a ha
    obtain ⟨i, rfl⟩ := hV (K.down_closed hs (Finset.singleton_subset_iff.mpr ha)
      (Finset.singleton_nonempty _))
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨t, _, ht⟩ := Finset.subset_image_iff.mp hsub
  exact ⟨t, ht⟩

def indexedFaces_degreeEquiv {n : ℕ} (K : Geometry.SimplicialComplex ℝ E)
    (v : Fin (n + 1) → E) (hv : Function.Injective v)
    (hV : K.vertices ⊆ Set.range v) (j : ℕ) :
    {s : Finset (Fin (n + 1)) // s ∈ (indexedFaces K v).faces ∧ s.card = j + 1} ≃
      {s : Finset E // s ∈ K.faces ∧ s.card = j + 1} := by
  classical
  apply Equiv.ofBijective (fun s => ⟨s.val.image v, s.property.1, by
    rw [Finset.card_image_of_injective _ hv]
    exact s.property.2⟩)
  constructor
  · intro s t h
    apply Subtype.ext
    exact Finset.image_injective hv (congrArg Subtype.val h)
  · intro s
    obtain ⟨t, ht⟩ := indexedFaces_image_contains K v hV s.val s.property.1
    refine ⟨⟨t, ?_, ?_⟩, Subtype.ext ht⟩
    · change t.image v ∈ K.faces
      rw [ht]
      exact s.property.1
    · rw [← Finset.card_image_of_injective t hv, ht]
      exact s.property.2

theorem finite_vertex_enumeration (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) :
    ∃ (m : ℕ) (v : Fin (m + 1) → E), Function.Injective v ∧
      K.vertices ⊆ Set.range v := by
  classical
  have hvertices : K.vertices.Finite := by
    rw [Geometry.SimplicialComplex.vertices_eq]
    exact hK.biUnion (fun s _ => s.finite_toSet)
  let W := insert (0 : E) hvertices.toFinset
  have hW : 0 < W.card := Finset.card_pos.mpr (Finset.insert_nonempty _ _)
  let e : Fin (W.card - 1 + 1) ≃ W :=
    (Finite.equivFinOfCardEq (α := W) (by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact (Nat.sub_add_cancel hW).symm)).symm
  refine ⟨W.card - 1, fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
  intro a ha
  have haW : a ∈ W := Finset.mem_insert_of_mem (hvertices.mem_toFinset.mpr ha)
  exact ⟨e.symm ⟨a, haW⟩, congrArg Subtype.val (e.apply_symm_apply ⟨a, haW⟩)⟩

end HodgeLean.Foundations.IntegralHomology.StageTwo
