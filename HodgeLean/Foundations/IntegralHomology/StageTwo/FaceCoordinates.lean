import HodgeLean.Foundations.IntegralHomology.StageTwo.FaceCover

/-! Standard coordinates for realized ordered faces.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

def faceVertexOrder {n : ℕ} (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    Fin (s.card - 1 + 1) ≃o s :=
  monoEquivOfFin s (by
    rw [Fintype.card_coe]
    exact (Nat.sub_add_cancel (Finset.card_pos.mpr hs)).symm)

def faceVertexMorphism {n : ℕ} (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    ⦋s.card - 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk ((OrderHom.Subtype.val (· ∈ s)).comp
    (faceVertexOrder s hs).toOrderEmbedding.toOrderHom)

def realizationCoordinates {n : ℕ} (A : (Δ[n] : SSet.{0}).Subcomplex) :
    C(SSet.toTop.obj (A : SSet.{0}), StdSimplex ℝ (Fin (n + 1))) :=
  ⟨fun x => SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map A.ι x),
    (SimplexCategory.toTopHomeo ⦋n⦌).continuous.comp (SSet.toTop.map A.ι).hom.continuous⟩

theorem simplexFace_coordinates {n : ℕ} (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (z : SSet.toTop.obj (Δ[s.card - 1] : SSet.{0})) :
    realizationCoordinates (SSet.stdSimplex.face s)
      (SSet.toTop.map (simplexFaceIso s hs).hom z) =
      StdSimplex.map (faceVertexMorphism s hs) (SimplexCategory.toTopHomeo _ z) := by
  have h : (simplexFaceIso s hs).hom ≫ (SSet.stdSimplex.face s).ι =
      SSet.stdSimplex.map (faceVertexMorphism s hs) :=
    simplexFaceIso_hom_inclusion s hs
  have hz := congrArg (fun f => SSet.toTop.map f z) h
  rw [Functor.map_comp] at hz
  exact (congrArg (SimplexCategory.toTopHomeo ⦋n⦌) hz).trans
    (SimplexCategory.toTopHomeo_naturality_apply _ z)

theorem range_faceVertexMorphism {n : ℕ} (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    Set.range (faceVertexMorphism s hs) = (s : Set (Fin (n + 1))) := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    exact (faceVertexOrder s hs i).property
  · intro ha
    refine ⟨(faceVertexOrder s hs).symm ⟨a, ha⟩, ?_⟩
    exact congrArg Subtype.val ((faceVertexOrder s hs).apply_symm_apply ⟨a, ha⟩)

theorem simplexFace_coordinates_range {n : ℕ}
    (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    Set.range (realizationCoordinates (SSet.stdSimplex.face s)) =
      setOf (fun p : StdSimplex ℝ (Fin (n + 1)) => ∀ a, a ∉ s → p.weights a = 0) := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨z, rfl⟩ :=
      (TopCat.homeoOfIso (SSet.toTop.mapIso (simplexFaceIso s hs))).surjective z
    change ∀ a, a ∉ s → (realizationCoordinates (SSet.stdSimplex.face s)
      (SSet.toTop.map (simplexFaceIso s hs).hom z)).weights a = 0
    rw [simplexFace_coordinates]
    intro a ha
    exact (StdSimplex.mem_range_map_iff (faceVertexMorphism s hs) _).mp
      ⟨_, rfl⟩ a (by rwa [range_faceVertexMorphism])
  · intro hp
    obtain ⟨w, hw⟩ := (StdSimplex.mem_range_map_iff (faceVertexMorphism s hs) p).mpr
      (fun a ha => hp a (by rwa [range_faceVertexMorphism] at ha))
    refine ⟨SSet.toTop.map (simplexFaceIso s hs).hom
      ((SimplexCategory.toTopHomeo _).symm w), ?_⟩
    rw [simplexFace_coordinates, Homeomorph.apply_symm_apply]
    exact hw

end HodgeLean.Foundations.IntegralHomology.StageTwo
