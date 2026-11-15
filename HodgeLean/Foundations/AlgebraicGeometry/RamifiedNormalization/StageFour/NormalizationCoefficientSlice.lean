import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ActualIntegralClosureChart
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.CoefficientChartSlice

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Original integral coefficient evaluations identify exactly the actual normalization slice chart and retain every base-chart coefficient. -/
theorem normalization_coefficient_slice_homeomorph
    {R A L : Type} [CommRing R] [CommRing A] [Field L]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (X B : Over (Spec ↧ℂ)) [IsSeparated B.hom]
    (η : Spec ↧L ⟶ X.left) [QuasiCompact η] [QuasiSeparated η]
    (b : X ⟶ B) (x : ComplexPoint B)
    (j : Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶ X) [IsOpenImmersion j.left]
    (hF : Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ j.left = η)
    (f : R →ₐ[ℂ] A)
    (c : Over.mk (ComplexPoint.affineSpecStructureMap R) ⟶ B) [Mono c]
    (hj : j ≫ b = Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap f) ≫ c)
    (φ : R →ₐ[ℂ] ℂ) (hx : Point.map c ((ComplexPoint.affineSpecEquiv R).symm φ) = x) :
    ∃ H : integralCoefficientFibre (L := L) f φ ≃ₜ
        {z : ComplexPoint (coveringSlice (s2b_normalizationMap X η) b x) //
          (Point.map (pullback.fst b x) (Point.map (sliceProjection (s2b_normalizationMap X η) b x) z)).left
            (IsLocalRing.closedPoint ℂ) ∈ Set.range j.left},
      ∀ z, ∃ y : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap A)),
        Point.map j y = Point.map (pullback.fst b x)
          (Point.map (sliceProjection (s2b_normalizationMap X η) b x) (H z).val) ∧
        ∀ a : A, ComplexPoint.affineSpecEquiv A y a =
          z.val (algebraMap A (integralClosure A L) a) := by
  obtain ⟨U, i, n, E, hi, hn, hb, hrange⟩ := actual_integral_closure_chart X η j hF
  haveI : IsOpenImmersion i.left := hi
  obtain ⟨Hc, hHc⟩ := integral_closure_chart_coefficient_fibre_homeomorph f φ U n E hb
  obtain ⟨Hs, hHs⟩ := coefficient_chart_covering_slice_homeomorph f
    (s2b_normalizationMap X η) b x i j n hn c hj φ hx hrange
  refine ⟨Hc.symm.trans Hs, ?_⟩
  intro z
  let u := Hc.symm z
  refine ⟨Point.map n u.val, ?_, ?_⟩
  · change Point.map j (Point.map n u.val) = Point.map (pullback.fst b x)
      (Point.map (sliceProjection (s2b_normalizationMap X η) b x) (Hs u).val)
    rw [← Point.map_comp_apply, hn, Point.map_comp_apply, ← hHs u,
      ← Point.map_comp_apply, pullback.condition, Point.map_comp_apply]
  · intro a
    have hs : (u.val.left ≫ E.hom) ≫ Spec.map
        (CommRingCat.ofHom (algebraMap A (integralClosure A L))) = (Point.map n u.val).left := by
      rw [Category.assoc, hb]
      rfl
    have he := congrArg (fun q : Spec ↧ℂ ⟶ Spec ↧A => (Spec.preimage q).hom) hs
    simp only [Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp] at he
    have hz := hHc u
    change (Hc (Hc.symm z)).val.toRingHom = _ at hz
    rw [Hc.apply_symm_apply] at hz
    have hev := DFunLike.congr_fun he a
    change Spec.homEquivRingHom (u.val.left ≫ E.hom)
      (algebraMap A (integralClosure A L) a) = ComplexPoint.affineSpecEquiv A (Point.map n u.val) a at hev
    rw [← hz] at hev
    exact hev.symm

end AlgebraicGeometry.RamifiedNormalization.StageFour
