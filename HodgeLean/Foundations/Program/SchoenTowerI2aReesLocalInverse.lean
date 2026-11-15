import HodgeLean.Foundations.Program.SchoenTowerI2aReesSchemeUniqueness
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A section of an actual integral Rees chart over an open target neighborhood
identifies that neighborhood with its entire inverse image in the Rees chart.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13, standard charts;
Mathlib, `IsOpenImmersion` stability under base change. -/
theorem s2v_i2a_rees_local_inverse
    (R : Type) [CommRing R] [IsDomain R] (x y : R) (hx : x ≠ 0)
    (Y V : Scheme.{0}) [IsIntegral V] (b : Y ⟶ Spec (CommRingCat.of R))
    (g : Spec (CommRingCat.of (s2t_reesChart (Ideal.span {x, y}) x)) ⟶ Y)
    (hg : g ≫ b = Spec.map (CommRingCat.ofHom (algebraMap R _)))
    (u : V ⟶ Y) [IsOpenImmersion u] [QuasiCompact u]
    (f : V ⟶ Spec (CommRingCat.of (s2t_reesChart (Ideal.span {x, y}) x)))
    (hf : f ≫ g = u) :
    IsIso (pullback.snd g u) ∧ IsOpenImmersion f := by
  let C := s2t_reesChart (Ideal.span {x, y}) x
  let base := Spec.map (CommRingCat.ofHom (algebraMap R C))
  let Z := pullback g u
  let w : Z ⟶ Spec (CommRingCat.of C) := pullback.fst g u
  let a : Z ⟶ V := pullback.snd g u
  let l : V ⟶ Z := pullback.lift f (𝟙 V) (by simpa using hf)
  letI : IsDomain (Localization.Away x) := Localization.Away.isDomain hx
  letI : Nonempty Z := ⟨l (Classical.choice (inferInstance : Nonempty V))⟩
  haveI : IsIntegral Z := isIntegral_of_isOpenImmersion w
  have hinj : Function.Injective (algebraMap R (Localization.Away x)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  have hxc : algebraMap R C x ≠ 0 := by
    intro H
    exact hx (hinj ((congrArg Subtype.val H).trans (map_zero _).symm))
  haveI : IsDominant w := ⟨w.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty w)⟩
  haveI : IsSchemeTheoreticallyDominant w := .of_isDominant w
  have hw : Function.Injective w.appTop.hom := by
    simpa only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
      TopologicalSpace.Opens.map_top] using w.app_injective ⊤
  have hb : (w ≫ base).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) ≠ 0 := by
    have hn := congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R C)))
    intro H
    have H' : w.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
        (algebraMap R C x)) = 0 := by
      have hn' : (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (algebraMap R C x) =
          base.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) :=
        RingHom.congr_fun hn x
      rw [hn']
      exact H
    have Hz := hw (H'.trans (map_zero _).symm)
    exact hxc ((Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.injective
      (Hz.trans (map_zero _).symm))
  have haf : a ≫ f = w := by
    apply s2v_i2a_pair_rees_scheme_map_unique R Z x y (w ≫ base) hb
    · change (pullback.snd g u ≫ f) ≫ base = pullback.fst g u ≫ base
      have hg' : g ≫ b = base := hg
      rw [← hg', Category.assoc, ← Category.assoc f, hf,
        ← Category.assoc, ← pullback.condition, Category.assoc]
    · rfl
  have hal : a ≫ l = 𝟙 Z := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, l, pullback.lift_fst, Category.id_comp] using haf
    · simp [l, a]
  have hla : l ≫ a = 𝟙 V := by simp [l, a]
  let e : Z ≅ V := ⟨a, l, hal, hla⟩
  haveI : IsIso a := e.isIso_hom
  haveI : IsIso l := e.isIso_inv
  refine ⟨inferInstance, ?_⟩
  have hlf : l ≫ w = f := by simp [l, w]
  rw [← hlf]
  infer_instance

end HodgeLean.Foundations.Program
