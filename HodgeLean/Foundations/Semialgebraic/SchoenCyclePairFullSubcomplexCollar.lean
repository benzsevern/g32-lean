import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairFullStar
import Mathlib.Topology.Category.TopPair
import Mathlib.Topology.Homotopy.TopCat.Basic
import Mathlib.SetTheory.Cardinal.Order

/-! Categorical neighbourhood data from full geometric subcomplexes.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory
universe u
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- A full subcomplex of a finite geometric complex has the required categorical collar data. -/
theorem s2e_pair_full_subcomplex_neighbourhood_deformation {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hDK : D.faces ⊆ K.faces)
    (hfull : ∀ s ∈ K.faces, (∀ a ∈ s, a ∈ D.vertices) → s ∈ D.faces) :
    let P := TopPair.ofSubset (X := TopCat.of K.space) {x | x.val ∈ D.space}
    ∃ (U : TopCat.{u}) (j : P.snd ⟶ U) (k : U ⟶ P.fst),
      j ≫ k = P.map ∧ Topology.IsOpenEmbedding k ∧
      ∃ q : U ⟶ P.snd, j ≫ q = 𝟙 P.snd ∧
        ∃ H : TopCat.Homotopy (𝟙 U) (q ≫ j),
          ∀ (t : unitInterval) (a : P.snd), H (t, j a) = j a := by
  classical
  letI : LinearOrder E := linearOrderOfSTO WellOrderingRel
  have hvertices : K.vertices.Finite := by
    rw [Geometry.SimplicialComplex.vertices_eq]
    exact hK.biUnion (fun s _ => s.finite_toSet)
  let V := hvertices.toFinset
  have hV (a : E) (ha : a ∈ K.vertices) : a ∈ V := hvertices.mem_toFinset.mpr ha
  obtain ⟨U, hU, hcontains, r, hrmarked, hrfixed, H, hfixed⟩ :=
    s2e_pair_full_star_deformation K D hK hDK hfull V hV
  let P := TopPair.ofSubset (X := TopCat.of K.space) {x | x.val ∈ D.space}
  let j : P.snd ⟶ TopCat.of U := TopCat.ofHom
    { toFun := fun a => ⟨a.val, hcontains a.val a.property⟩
      continuous_toFun := continuous_subtype_val.subtype_mk _ }
  let k : TopCat.of U ⟶ P.fst := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let q : TopCat.of U ⟶ P.snd := TopCat.ofHom
    { toFun := fun x => ⟨(r x).val, hrmarked x⟩
      continuous_toFun := (continuous_subtype_val.comp r.continuous).subtype_mk _ }
  refine ⟨TopCat.of U, j, k, ?_, hU.isOpenEmbedding_subtypeVal, q, ?_, ?_⟩
  · rfl
  · apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    change (r (j a)).val = a.val
    exact congrArg (fun z : U => z.val) (hrfixed (j a) a.property)
  · refine ⟨{ toContinuousMap := H.toContinuousMap
              map_zero_left := H.map_zero_left
              map_one_left := ?_ }, ?_⟩
    · intro x
      exact (H.map_one_left x).trans (Subtype.ext rfl)
    · intro t a
      exact hfixed t (j a) a.property

end Semialgebraic.CompatibleTriangulation.Helpers
