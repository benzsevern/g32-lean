import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProperNormalSection
import HodgeLean.Foundations.Program.SchoenTowerFibreTopology

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A labelled selector fibre and a compatible proper parameter morphism produce an actual component section with its exact point coordinates. -/
theorem selector_fibre_component_section
    {I : Type} (F C Y : Over (Spec ↧ℂ))
    [IsProper F.hom] [LocallyOfFiniteType F.hom] [IsSeparated C.hom]
    [IsIntegral Y.left] [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (hY : zmtiso_IsNormal Y.left)
    (q : F ⟶ C) (r : F ⟶ Y)
    (b : I → ComplexPoint C) (hb : Function.Injective b)
    (E : ComplexPoint F ≃ I × ComplexPoint Y)
    (hq : ∀ z, Point.map q z = b (E z).1)
    (hr : ∀ z, Point.map r z = (E z).2) (i : I) :
    ∃ j : Y ⟶ F, IsClosedImmersion j.left ∧
      ∀ y : ComplexPoint Y, E (Point.map j y) = (i, y) := by
  let Z := pullback q (b i)
  let a : Z ⟶ F := pullback.fst q (b i)
  let H := s2v_separatedPointFibreHomeomorph q (b i)
  haveI : IsClosedImmersion a.left := s2v_schemeFibre_closedImmersion q (b i)
  haveI : Mono a := Over.mono_of_mono_left a
  haveI : IsProper Z.hom := a.w ▸ (inferInstance : IsProper (a.left ≫ F.hom))
  haveI : LocallyOfFiniteType Z.hom := a.w ▸ (inferInstance : LocallyOfFiniteType (a.left ≫ F.hom))
  let f := a ≫ r
  haveI : IsProper (f.left ≫ Y.hom) := f.w.symm ▸ (inferInstance : IsProper Z.hom)
  haveI : IsProper f.left := IsProper.of_comp f.left Y.hom
  have hlabel (z : ComplexPoint Z) : (E (Point.map a z)).1 = i := by
    apply hb
    exact (hq (Point.map a z)).symm.trans (H z).property
  have hbij : Function.Bijective (Point.map f) := by
    constructor
    · intro z₁ z₂ he
      have hsecond : (E (Point.map a z₁)).2 = (E (Point.map a z₂)).2 := by
        change Point.map (a ≫ r) z₁ = Point.map (a ≫ r) z₂ at he
        rw [Point.map_comp_apply, Point.map_comp_apply, hr, hr] at he
        exact he
      have hp := E.injective (Prod.ext ((hlabel z₁).trans (hlabel z₂).symm) hsecond)
      exact (cancel_mono a).mp hp
    · intro y
      let z₀ := E.symm (i, y)
      have hz₀ : Point.map q z₀ = b i := by
        rw [hq]
        change b (E (E.symm (i, y))).1 = _
        rw [E.apply_symm_apply]
      let z := H.symm ⟨z₀, hz₀⟩
      have hz : Point.map a z = z₀ := congrArg Subtype.val (H.apply_symm_apply ⟨z₀, hz₀⟩)
      refine ⟨z, ?_⟩
      change Point.map (a ≫ r) z = y
      rw [Point.map_comp_apply, hz, hr]
      exact congrArg Prod.snd (E.apply_symm_apply (i, y))
  obtain ⟨j₀, hj₀, hsection, _⟩ := proper_normal_point_bijective_section Z Y f hY hbij
  haveI : IsClosedImmersion j₀.left := hj₀
  refine ⟨j₀ ≫ a, ?_, ?_⟩
  · change IsClosedImmersion (j₀.left ≫ a.left)
    infer_instance
  · intro y
    rw [Point.map_comp_apply]
    apply Prod.ext
    · exact hlabel (Point.map j₀ y)
    · have hs : Point.map f (Point.map j₀ y) = y := by
        rw [← Point.map_comp_apply, hsection, Point.map_id]
      rw [Point.map_comp_apply] at hs
      exact (hr (Point.map a (Point.map j₀ y))).symm.trans hs

end AlgebraicGeometry.RamifiedNormalization.StageFour
