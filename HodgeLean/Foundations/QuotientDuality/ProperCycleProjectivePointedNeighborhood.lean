import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectivePointedTriangulation
import HodgeLean.Foundations.QuotientDuality.ProperCycleFullStarAvoidsVertex
import Mathlib.Topology.Category.TopPair
import Mathlib.Topology.Homotopy.TopCat.Basic

/-! # Actual projective boundary neighborhoods avoiding an original outside point -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.QuotientDuality

/-- An original closed projective support has an actual open strong deformation neighborhood avoiding any specified original point outside that support.
Source: properCycle_projective_pointed_full_triangulation; properCycle_full_star_deformation_avoiding_vertex.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_pointed_neighborhood_deformation
    (X Z : Over (Spec ↧ℂ)) [IsProjective X.hom] (i : Z ⟶ X)
    [IsClosedImmersion i.left] (x : ComplexPoint X) (hx : x ∉ Set.range (Point.map i)) :
    let P := TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) (Set.range (Point.map i))
    ∃ (U : TopCat.{0}) (j : P.snd ⟶ U) (k : U ⟶ P.fst),
      j ≫ k = P.map ∧ Topology.IsOpenEmbedding k ∧ x ∉ Set.range k ∧
      ∃ q : U ⟶ P.snd, j ≫ q = 𝟙 P.snd ∧
        ∃ H : TopCat.Homotopy (𝟙 U) (q ≫ j),
          ∀ (t : unitInterval) (z : P.snd), H (t, j z) = j z := by
  classical
  obtain ⟨a, K, D, hK, hDK, hfull, h, hmark, hp, hpD⟩ :=
    properCycle_projective_pointed_full_triangulation X Z i x hx
  letI : LinearOrder (EuclideanSpace ℝ (Fin a)) := IsWellOrder.linearOrder WellOrderingRel
  have hvfinite : K.vertices.Finite :=
    Set.Finite.preimage (fun _ _ _ _ he => Finset.singleton_injective he) hK
  let V := hvfinite.toFinset
  have hV : ∀ b ∈ K.vertices, b ∈ V := fun b hb => hvfinite.mem_toFinset.mpr hb
  obtain ⟨N, hN, hcontains, havoid, r, hrmarked, hrfixed, H, hfixed⟩ :=
    properCycle_full_star_deformation_avoiding_vertex K D hK hDK hfull V hV
      (h.symm x).val hp hpD
  let P := TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) (Set.range (Point.map i))
  let j : P.snd ⟶ TopCat.of N := TopCat.ofHom
    { toFun := fun z => ⟨h.symm z.val, hcontains _ ((hmark _).mp (by simpa using z.property))⟩
      continuous_toFun := (h.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
  let k : TopCat.of N ⟶ P.fst := TopCat.ofHom
    ⟨fun u => h u.val, h.continuous.comp continuous_subtype_val⟩
  let q : TopCat.of N ⟶ P.snd := TopCat.ofHom
    { toFun := fun u => ⟨h (r u).val, (hmark _).mpr (hrmarked u)⟩
      continuous_toFun := (h.continuous.comp
        (continuous_subtype_val.comp r.continuous)).subtype_mk _ }
  have hj (z : P.snd) : (j z).val.val ∈ D.space := by
    change (h.symm z.val).val ∈ D.space
    exact (hmark _).mp (by simpa using z.property)
  have heq (u : N) : j (q u) = r u := by
    apply Subtype.ext
    change h.symm (h (r u).val) = (r u).val
    exact h.symm_apply_apply _
  refine ⟨TopCat.of N, j, k, ?_, ?_, ?_, q, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro z
    exact h.apply_symm_apply z.val
  · exact h.isOpenEmbedding.comp hN.isOpenEmbedding_subtypeVal
  · rintro ⟨u, hu⟩
    have hu' : u.val = h.symm x := h.injective (hu.trans (h.apply_symm_apply x).symm)
    exact havoid u.val (congrArg Subtype.val hu') u.property
  · apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    change h (r (j z)).val = z.val
    rw [hrfixed (j z) (hj z)]
    exact h.apply_symm_apply z.val
  · refine ⟨{ toContinuousMap := H.toContinuousMap
              map_zero_left := H.map_zero_left
              map_one_left := fun u => (H.map_one_left u).trans (heq u).symm }, ?_⟩
    intro t z
    exact hfixed t (j z) (hj z)

end HodgeLean.Foundations.QuotientDuality
