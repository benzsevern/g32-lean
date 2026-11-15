import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineNormalizationRestriction
import HodgeLean.Foundations.Program.SchoenTowerI2aFieldOpenFactor
import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChart

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A nonempty actual ratio chart inherits a faithful embedding in the specified original field, with the original coefficients and literal ratio. -/
theorem original_affine_chart_field
    {R L : Type} [CommRing R] [Field L] {Y Z : Scheme} [IsIntegral Y]
    (u v : R) [Nonempty (Spec ↧(RegularPairChart.ring u v))]
    (η : Spec ↧L ⟶ Y) [IsDominant η] [QuasiCompact η] [QuasiSeparated η]
    (π : Y ⟶ Z) (c : Spec ↧R ⟶ Z) [Mono c]
    (j : Spec ↧(RegularPairChart.ring u v) ⟶ Y) [IsOpenImmersion j]
    (hj : j ≫ π = Spec.map (CommRingCat.ofHom (RegularPairChart.coeff u v)) ≫ c)
    (f : R →+* L) (hf : η ≫ π = Spec.map (CommRingCat.ofHom f) ≫ c) (hv : f v ≠ 0) :
    ∃ F : RegularPairChart.ring u v →+* L,
      Function.Injective F ∧ F.comp (RegularPairChart.coeff u v) = f ∧
      F (RegularPairChart.ratio u v) = f u / f v ∧
      ∃ hFj : Spec.map (CommRingCat.ofHom F) ≫ j = η,
      ∃ E : pullback η.fromNormalization j ≅ Spec ↧(normalizedChart F),
        StageThree.restrictedFieldPoint η j (Spec.map (CommRingCat.ofHom F))
          hFj ≫ E.hom = Spec.map (CommRingCat.ofHom (normalizedChart F).subtype) ∧
        E.hom ≫ Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff F)) =
          pullback.snd η.fromNormalization j := by
  obtain ⟨q, ⟨hq, hdom⟩, _⟩ :=
    HodgeLean.Foundations.Program.s2v_i2a_dominant_field_point_open_factor j η
  let F := (Spec.preimage q).hom
  have hF : Spec.map (CommRingCat.ofHom F) = q := Spec.map_preimage q
  have hFj : Spec.map (CommRingCat.ofHom F) ≫ j = η := by rw [hF, hq]
  have hc : F.comp (RegularPairChart.coeff u v) = f := by
    change (CommRingCat.ofHom (F.comp (RegularPairChart.coeff u v))).hom =
      (CommRingCat.ofHom f).hom
    apply CommRingCat.hom_ext_iff.mp
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (F.comp (RegularPairChart.coeff u v))) = _
    apply (cancel_mono c).mp
    rw [show CommRingCat.ofHom (F.comp (RegularPairChart.coeff u v)) =
      CommRingCat.ofHom (RegularPairChart.coeff u v) ≫ CommRingCat.ofHom F from rfl,
      Spec.map_comp, Category.assoc, ← hj, ← Category.assoc, hFj, hf]
  let e := (Scheme.ΓSpecIso ↧(RegularPairChart.ring u v)).commRingCatIsoToRingEquiv
  have he : F.comp e.toRingHom = StageThree.fieldCoeff q := by
    apply CommRingCat.hom_ext_iff.mp
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (F.comp e.toRingHom)) =
      Spec.map (CommRingCat.ofHom (StageThree.fieldCoeff q))
    rw [StageThree.fieldCoeff_spec]
    change Spec.map ((Scheme.ΓSpecIso ↧(RegularPairChart.ring u v)).hom ≫ CommRingCat.ofHom F) = _
    rw [Spec.map_comp, SpecMap_ΓSpecIso_hom, hF]
  have hinj := StageThree.coefficient_embedding η j q hq
  have hi : Function.Injective F := by
    intro a b hab
    apply e.symm.injective
    apply hinj
    rw [← he]
    change F (e (e.symm a)) = F (e (e.symm b))
    simpa only [e.apply_symm_apply] using hab
  have hratio : F (RegularPairChart.ratio u v) = f u / f v := by
    apply (eq_div_iff hv).mpr
    have h := congrArg F (RegularPairChart.chart_relation u v)
    rw [map_mul] at h
    have hcoeff (a : R) : F (RegularPairChart.coeff u v a) = f a := DFunLike.congr_fun hc a
    change F (RegularPairChart.coeff u v u) =
      F (RegularPairChart.ratio u v) * F (RegularPairChart.coeff u v v) at h
    rw [hcoeff, hcoeff] at h
    exact h.symm
  obtain ⟨E, hE, hb⟩ := affine_normalization_restriction η j F hFj
  exact ⟨F, hi, hc, hratio, hFj, E, hE, hb⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
