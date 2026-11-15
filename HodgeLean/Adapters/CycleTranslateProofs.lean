import HodgeLean.Adapters.CycleTranslateDefs

/-! # Translation bookkeeping: proofs of the frozen statements -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Adapters

/-- The pullback of an ideal sheaf along an isomorphism is its pushforward along the inverse. -/
private theorem hc9k_comap_hom_eq_map_inv {X Z : Scheme} (e : X ≅ Z) (I : Z.IdealSheafData) :
    I.comap e.hom = I.map e.inv := by
  have hcomap (J : X.IdealSheafData) : (J.comap e.inv).comap e.hom = J := by
    rw [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id, Scheme.IdealSheafData.comap_id]
  have hcomap' (J : Z.IdealSheafData) : (J.comap e.hom).comap e.inv = J := by
    rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]
  apply le_antisymm
  · rw [Scheme.IdealSheafData.le_map_iff_comap_le, hcomap']
  · have h : ((I.map e.inv).comap e.inv).comap e.hom ≤ I.comap e.hom :=
      Scheme.IdealSheafData.comap_mono e.hom
        (Scheme.IdealSheafData.comap_map_le (f := e.inv) (I := I))
    rwa [hcomap] at h

/-- The inverse ideal of a prime component along an isomorphism. -/
private theorem hc9k_inverseIdeal_iso {X Z : Scheme} (e : X ≅ Z) (x : Z) :
    ccm3_inverseIdeal e.hom x = ccm3_primeIdeal X (e.inv x) := by
  rw [ccm3_inverseIdeal, ccm3_primeIdeal, ccm3_primeIdeal, hc9k_comap_hom_eq_map_inv,
    Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext1
  simp only [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_mk]
  rw [closure_image_closure e.inv.continuous, Set.image_singleton]

private theorem hc9k_vanishingIdeal_subscheme_isReduced (X : Scheme)
    (Z : TopologicalSpace.Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let : ∀ U : (Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.I₀,
      IsReduced ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X U) :=
    fun U ↦ by
      change X.affineOpens at U
      let : _root_.IsReduced
          ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.X U) := by
        change _root_.IsReduced (Γ(X, U) ⧸
          (Scheme.IdealSheafData.vanishingIdeal Z).ideal U)
        rw [← Ideal.isRadical_iff_quotient_reduced]
        rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
        exact PrimeSpectrum.isRadical_vanishingIdeal _
      change IsReduced
        (Spec ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.X U))
      infer_instance
  exact IsReduced.of_openCover _
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover

/-- When the inverse ideal is the prime ideal of `z`, the flat pullback is `z` with
coefficient one. -/
private theorem hc9k_flatPullbackPrime_of_inverseIdeal {X Z : Scheme} [DecidableEq X]
    (f : X ⟶ Z) (x : Z) (z : X) (h : ccm3_inverseIdeal f x = ccm3_primeIdeal X z) :
    ccm3_flatPullbackPrime f x = Function.locallyFinsuppWithin.single z (1 : ℚ) := by
  let I := ccm3_inverseIdeal f x
  have hs : (I.support : Set X) = closure ({z} : Set X) := by
    simp only [I, h, ccm3_primeIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hz : z ∈ (I.support : Set X) := hs ▸ subset_closure (Set.mem_singleton z)
  let w₀ : I.subscheme := ⟨z, hz⟩
  have hgen (w : I.subscheme) : w₀ ⤳ w := by
    have hw : z ⤳ w.1 := by
      rw [specializes_iff_mem_closure, ← hs]
      exact w.2
    exact (Topology.IsInducing.subtypeVal (t := (I.support : Set X))).specializes_iff.mp hw
  have hclosure : closure ({w₀} : Set I.subscheme) = Set.univ :=
    Set.eq_univ_of_forall fun w ↦ specializes_iff_mem_closure.mp (hgen w)
  have hcomp (w : I.subscheme) :
      closure ({w} : Set I.subscheme) ∈ irreducibleComponents I.subscheme ↔ w = w₀ := by
    constructor
    · intro hw
      have hle := hw.2 (isIrreducible_singleton (x := w₀)).closure
        (show closure ({w} : Set I.subscheme) ⊆ closure ({w₀} : Set I.subscheme) by
          rw [hclosure]; exact Set.subset_univ _)
      have hw₀ : w ⤳ w₀ := specializes_iff_mem_closure.mpr
        (hle (subset_closure (Set.mem_singleton w₀)))
      exact (hw₀.antisymm (hgen w)).eq
    · rintro rfl
      exact ⟨isIrreducible_singleton.closure, fun T _ _ ↦ by
        rw [hclosure]; exact Set.subset_univ _⟩
  let : IsReduced I.subscheme := by
    change IsReduced (ccm3_inverseIdeal f x).subscheme
    rw [h]
    exact hc9k_vanishingIdeal_subscheme_isReduced X _
  have hlen : ccm3_genericLength f x w₀ = 1 := by
    have hfield : IsField (I.subscheme.presheaf.stalk w₀) :=
      isField_stalk_of_closure_mem_irreducibleComponents I.subscheme w₀ ((hcomp w₀).2 rfl)
    let : Field (I.subscheme.presheaf.stalk w₀) := hfield.toField
    unfold ccm3_genericLength
    exact Module.length_eq_one _ _
  classical
  rw [ccm3_flatPullbackPrime]
  rw [finsum_eq_single _ w₀ (fun w hw ↦ by rw [if_neg (fun hc ↦ hw ((hcomp w).1 hc))])]
  rw [if_pos ((hcomp w₀).2 rfl), hlen]
  apply Function.locallyFinsuppWithin.ext
  intro u
  have hι : (ccm3_inverseIdeal f x).subschemeι w₀ = z := rfl
  simp only [Function.locallyFinsuppWithin.single_apply]
  by_cases hu : u = z
  · rw [if_pos (hu.trans hι.symm), if_pos hu]
    simp
  · rw [if_neg (fun h' ↦ hu (h'.trans hι)), if_neg hu]

theorem hc9k_translate_inverseIdeal_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    (t : ComplexPoint X) (y : X.left) :
    ccm3_inverseIdeal (GrpObj.mulRight t).hom.left y =
      ccm3_primeIdeal X.left (hc9k_translatePoint X t y) :=
  hc9k_inverseIdeal_iso ((Over.forget _).mapIso (GrpObj.mulRight t)) y

theorem hc9k_translate_flatPullbackPrime_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [DecidableEq X.left] (t : ComplexPoint X) (y : X.left) :
    ccm3_flatPullbackPrime (GrpObj.mulRight t).hom.left y =
      Function.locallyFinsuppWithin.single (hc9k_translatePoint X t y) (1 : ℚ) :=
  hc9k_flatPullbackPrime_of_inverseIdeal _ y _ (hc9k_translate_inverseIdeal_aux X t y)

theorem hc9k_translate_coheight_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    (t : ComplexPoint X) (y : X.left) :
    Order.coheight (hc9k_translatePoint X t y) = Order.coheight y := by
  let φ : X.left ≃ₜ X.left := Scheme.homeoOfIso ((Over.forget _).mapIso (GrpObj.mulRight t)).symm
  let ψ : X.left ≃o X.left :=
    { toEquiv := φ.toEquiv
      map_rel_iff' := φ.isInducing.specializes_iff }
  exact Order.coheight_orderIso ψ y

theorem hc9k_translate_cycleClass_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (t : ComplexPoint X) (q : ℕ) (y : X.left) (hy : Order.coheight y = q) :
    ccm3_cycleClass X q (ccm3_flatPullbackPrime (GrpObj.mulRight t).hom.left y) =
      cycleComponentSheafClass X y hy := by
  classical
  let c : AlgebraicCycle X.left ℚ := Function.locallyFinsuppWithin.single y 1
  have hc : ∀ x : X.left, c x ≠ 0 → Order.coheight x = q := by
    intro x hx
    by_cases hxy : x = y
    · rw [hxy, hy]
    · exact (hx (by simp [c, Function.locallyFinsuppWithin.single_apply, hxy])).elim
  have hpull : ccm3_flatPullback (GrpObj.mulRight t).hom.left c =
      ccm3_flatPullbackPrime (GrpObj.mulRight t).hom.left y := by
    unfold ccm3_flatPullback
    rw [finsum_eq_single _ y (fun x hx ↦ by
      apply Function.locallyFinsuppWithin.ext
      intro z
      simp only [c, Function.locallyFinsuppWithin.mapRange_apply,
        Function.locallyFinsuppWithin.single_apply, if_neg hx, zero_mul]
      rfl)]
    apply Function.locallyFinsuppWithin.ext
    intro z
    simp only [c, Function.locallyFinsuppWithin.mapRange_apply,
      Function.locallyFinsuppWithin.single_apply, ↓reduceIte, one_mul]
  have hclass : ccm3_cycleClass X q c = cycleComponentSheafClass X y hy := by
    unfold ccm3_cycleClass
    change (∑ᶠ z : {z : X.left // Order.coheight z = q},
      c z.1 • (cycleComponentSheafClass X z.1 z.2 : HodgeLean.RealDefs.HQ X (2 * q))) = _
    rw [finsum_eq_single _ ⟨y, hy⟩ (fun z hz ↦ by
      rw [show c z.1 = 0 by
        simp only [c, Function.locallyFinsuppWithin.single_apply]
        exact if_neg fun h ↦ hz (Subtype.ext h)]
      exact zero_smul _ _)]
    simp only [c, Function.locallyFinsuppWithin.single_apply, ↓reduceIte, one_smul]
  rw [← hpull, ccm11_translated_cycleClass X t q c hc, hclass]

end HodgeLean.Adapters
