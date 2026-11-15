import HodgeLean.Foundations.IntegralHomology.StageTwo.FaceRealization

/-! Face covers of ordered simplicial models and their realizations.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

def faceInclusion {n : ℕ} (P : PreAbstractSimplicialComplex (Fin (n + 1)))
    (s : P.faces) : (SSet.stdSimplex.face s.val : SSet.{0}) ⟶ (faceComplex P : SSet.{0}) :=
  SSet.Subcomplex.homOfLE (le_iSup (fun t : P.faces => SSet.stdSimplex.face t.val) s)

def faceCover {n : ℕ} (P : PreAbstractSimplicialComplex (Fin (n + 1))) :
    (∐ fun s : P.faces => (SSet.stdSimplex.face s.val : SSet.{0})) ⟶
      (faceComplex P : SSet.{0}) :=
  Sigma.desc (faceInclusion P)

theorem faceCover_epi {n : ℕ} (P : PreAbstractSimplicialComplex (Fin (n + 1))) :
    Epi (faceCover P) := by
  constructor
  intro Z f g h
  ext m x
  have hx := x.property
  change x.val ∈ (⨆ s : P.faces, SSet.stdSimplex.face s.val).obj m at hx
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hx
  obtain ⟨s, hs⟩ := hx
  have h' : faceInclusion P s ≫ f = faceInclusion P s ≫ g := by
    simpa only [faceCover, Category.assoc, Sigma.ι_comp_desc_assoc] using
      congrArg (fun a => Sigma.ι (fun s : P.faces => (SSet.stdSimplex.face s.val : SSet.{0})) s ≫ a) h
  exact ConcreteCategory.congr_hom (congrArg (fun a => a.app m) h') ⟨x.val, hs⟩

theorem realized_face_cover {n : ℕ} (P : PreAbstractSimplicialComplex (Fin (n + 1)))
    (x : SSet.toTop.obj (faceComplex P : SSet.{0})) :
    ∃ (s : P.faces) (y : SSet.toTop.obj (SSet.stdSimplex.face s.val : SSet.{0})),
      SSet.toTop.map (faceInclusion P s) y = x := by
  haveI := faceCover_epi P
  let G := SSet.toTop.{0} ⋙ forget TopCat
  have hf : Function.Surjective (G.map (faceCover P)) :=
    (epi_iff_surjective _).mp inferInstance
  obtain ⟨z, hz⟩ := hf x
  let F := fun s : P.faces => (SSet.stdSimplex.face s.val : SSet.{0})
  let C := Cofan.mk (G.obj (∐ F)) (fun s => G.map (Sigma.ι F s))
  have hc : IsColimit C := isColimitCofanMkObjOfIsColimit G F _ (coproductIsCoproduct F)
  obtain ⟨s, y, hy⟩ := Cofan.inj_jointly_surjective_of_isColimit hc z
  refine ⟨s, y, ?_⟩
  have hw : G.map (Sigma.ι F s) ≫ G.map (faceCover P) =
      G.map (faceInclusion P s) := by
    rw [← G.map_comp]
    congr 1
    exact Sigma.ι_comp_desc _ _
  exact (ConcreteCategory.congr_hom hw y).symm.trans
    ((congrArg (G.map (faceCover P)) hy).trans hz)

theorem realized_face_complex_compact {n : ℕ}
    (P : PreAbstractSimplicialComplex (Fin (n + 1))) :
    CompactSpace (SSet.toTop.obj (faceComplex P : SSet.{0})) := by
  letI (s : P.faces) : CompactSpace
      (SSet.toTop.obj (SSet.stdSimplex.face s.val : SSet.{0})) := by
    have hs := (P.isRelLowerSet_faces s.property).1
    letI : CompactSpace (SSet.toTop.obj (Δ[s.val.card - 1] : SSet.{0})) :=
      (SimplexCategory.toTopHomeo _).symm.compactSpace
    exact (TopCat.homeoOfIso (SSet.toTop.mapIso (simplexFaceIso s.val hs))).compactSpace
  let g : (Σ s : P.faces, SSet.toTop.obj (SSet.stdSimplex.face s.val : SSet.{0})) →
      SSet.toTop.obj (faceComplex P : SSet.{0}) :=
    fun p => SSet.toTop.map (faceInclusion P p.1) p.2
  have hg : Continuous g := continuous_sigma (fun s =>
    (SSet.toTop.map (faceInclusion P s)).hom.continuous)
  exact Function.Surjective.compactSpace hg (fun x => by
    obtain ⟨s, y, hy⟩ := realized_face_cover P x
    exact ⟨⟨s, y⟩, hy⟩)

end HodgeLean.Foundations.IntegralHomology.StageTwo
