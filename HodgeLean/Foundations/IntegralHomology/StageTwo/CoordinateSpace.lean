import HodgeLean.Foundations.IntegralHomology.StageTwo.FaceCoordinates

/-! The barycentric coordinate space of a finite ordered face complex.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

theorem faceInclusion_coordinates {n : ℕ}
    (P : PreAbstractSimplicialComplex (Fin (n + 1))) (s : P.faces)
    (z : SSet.toTop.obj (SSet.stdSimplex.face s.val : SSet.{0})) :
    realizationCoordinates (faceComplex P) (SSet.toTop.map (faceInclusion P s) z) =
      realizationCoordinates (SSet.stdSimplex.face s.val) z := by
  have h : faceInclusion P s ≫ (faceComplex P).ι = (SSet.stdSimplex.face s.val).ι := rfl
  have hz := congrArg (fun f => SSet.toTop.map f z) h
  rw [Functor.map_comp] at hz
  exact congrArg (SimplexCategory.toTopHomeo ⦋n⦌) hz

theorem faceComplex_coordinates_range {n : ℕ}
    (P : PreAbstractSimplicialComplex (Fin (n + 1))) :
    Set.range (realizationCoordinates (faceComplex P)) =
      setOf (fun p : StdSimplex ℝ (Fin (n + 1)) =>
        ∃ s ∈ P.faces, ∀ a, a ∉ s → p.weights a = 0) := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨s, z, rfl⟩ := realized_face_cover P z
    rw [faceInclusion_coordinates]
    refine ⟨s.val, s.property, ?_⟩
    have hm : realizationCoordinates (SSet.stdSimplex.face s.val) z ∈
        Set.range (realizationCoordinates (SSet.stdSimplex.face s.val)) := ⟨z, rfl⟩
    rw [simplexFace_coordinates_range s.val (P.isRelLowerSet_faces s.property).1] at hm
    exact hm
  · rintro ⟨s, hs, hp⟩
    have hm : p ∈ Set.range (realizationCoordinates (SSet.stdSimplex.face s)) := by
      rw [simplexFace_coordinates_range s (P.isRelLowerSet_faces hs).1]
      exact hp
    obtain ⟨z, hz⟩ := hm
    refine ⟨SSet.toTop.map (faceInclusion P ⟨s, hs⟩) z, ?_⟩
    exact (faceInclusion_coordinates P ⟨s, hs⟩ z).trans hz

abbrev faceCoordinateSpace {n : ℕ} (P : PreAbstractSimplicialComplex (Fin (n + 1))) : Type :=
  {p : StdSimplex ℝ (Fin (n + 1)) // ∃ s ∈ P.faces, ∀ a, a ∉ s → p.weights a = 0}

theorem faceComplex_coordinates_embedding {n : ℕ}
    (P : PreAbstractSimplicialComplex (Fin (n + 1))) :
    Topology.IsEmbedding (realizationCoordinates (faceComplex P)) := by
  letI : T2Space (StdSimplex ℝ (Fin (n + 1))) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).t2Space
  haveI := realized_face_complex_compact P
  have hi : Function.Injective (SSet.toTop.map (faceComplex P).ι) :=
    (TopCat.mono_iff_injective _).mp
      (HodgeLean.Foundations.Program.c1a5_realization_map_mono (faceComplex P).ι)
  exact ((realizationCoordinates (faceComplex P)).continuous.isClosedEmbedding
    ((SimplexCategory.toTopHomeo ⦋n⦌).injective.comp hi)).isEmbedding

def faceCoordinateHomeomorph {n : ℕ}
    (P : PreAbstractSimplicialComplex (Fin (n + 1))) :
    SSet.toTop.obj (faceComplex P : SSet.{0}) ≃ₜ faceCoordinateSpace P :=
  (faceComplex_coordinates_embedding P).toHomeomorph.trans
    (Homeomorph.setCongr (faceComplex_coordinates_range P))

end HodgeLean.Foundations.IntegralHomology.StageTwo
