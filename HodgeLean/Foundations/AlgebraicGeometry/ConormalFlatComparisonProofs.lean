import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineSchemeComparison
import HodgeLean.Foundations.AlgebraicGeometry.ConormalOpenComparison
import HodgeLean.Foundations.AlgebraicGeometry.ConormalLocalIsomorphism

/-! # Flat cartesian comparison for the actual kernel ideal sheaves
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Conormal

/-- The natural flat ideal comparison is invertible when the original ambient scheme is affine. -/
lemma idealPullbackMap_isIso_of_affine_target
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i'] [IsAffine W]
    (f : W' ⟶ W) [Flat f] (g : Q' ⟶ Q) (sq : IsPullback g i' i f) :
    IsIso (idealPullbackMap i i' f g sq.w) := by
  apply moduleMap_isIso_of_open_neighborhoods
  intro x
  obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset (X := W')
    (U := ⊤) (x := x) (show x ∈ (⊤ : W'.Opens) from trivial)
  have : IsAffine V.toScheme := hV
  have sqV : IsPullback ((i' ⁻¹ᵁ V).ι ≫ g) (i' ∣_ V) i (V.ι ≫ f) :=
    (isPullback_morphismRestrict i' V).flip.paste_horiz sq
  have : IsIso (idealPullbackMap i (i' ∣_ V) (V.ι ≫ f) ((i' ⁻¹ᵁ V).ι ≫ g) sqV.w) :=
    idealPullbackMap_isIso_of_isAffine i (i' ∣_ V) (V.ι ≫ f) _ sqV
  have : IsIso (idealPullbackMap i' (i' ∣_ V) V.ι (i' ⁻¹ᵁ V).ι
      (morphismRestrict_ι i' V).symm) := idealPullbackMap_open_isIso i' V
  exact ⟨V, hx, idealPullbackMap_map_isIso_of_comp i i' (i' ∣_ V) f V.ι g
    (i' ⁻¹ᵁ V).ι sq.w (morphismRestrict_ι i' V).symm sqV.w⟩

/-- The natural ideal comparison is invertible for every flat cartesian square of immersions. -/
lemma idealPullbackMap_isIso_of_flat
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (f : W' ⟶ W) [Flat f] (g : Q' ⟶ Q) (sq : IsPullback g i' i f) :
    IsIso (idealPullbackMap i i' f g sq.w) := by
  apply moduleMap_isIso_of_open_neighborhoods
  intro x
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (X := W)
    (U := ⊤) (x := f x) (show f x ∈ (⊤ : W.Opens) from trivial)
  have : IsAffine U.toScheme := hU
  let V := f ⁻¹ᵁ U
  have hp : i' ⁻¹ᵁ V = g ⁻¹ᵁ (i ⁻¹ᵁ U) := by
    change i' ⁻¹ᵁ (f ⁻¹ᵁ U) = g ⁻¹ᵁ (i ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, ← sq.w, Scheme.Hom.comp_preimage]
  let gU := g.resLE (i ⁻¹ᵁ U) (i' ⁻¹ᵁ V) hp.le
  have sqU : IsPullback gU (i' ∣_ V) (i ∣_ U) (f ∣_ U) := by
    have hs := Scheme.Hom.isPullback_resLE sq (US := U) (UT := V) (UX := i ⁻¹ᵁ U)
      (UY := i' ⁻¹ᵁ V) le_rfl le_rfl (by rw [← hp, inf_idem])
    simpa only [V, Scheme.Hom.resLE_eq_morphismRestrict] using hs
  have hLocal : IsIso (idealPullbackMap (i ∣_ U) (i' ∣_ V) (f ∣_ U) gU sqU.w) :=
    idealPullbackMap_isIso_of_affine_target (i ∣_ U) (i' ∣_ V) (f ∣_ U) gU sqU
  have sqNew : IsPullback (gU ≫ (i ⁻¹ᵁ U).ι) (i' ∣_ V) i ((f ∣_ U) ≫ U.ι) :=
    sqU.paste_horiz (isPullback_morphismRestrict i U).flip
  have sqOld : IsPullback ((i' ⁻¹ᵁ V).ι ≫ g) (i' ∣_ V) i (V.ι ≫ f) :=
    (isPullback_morphismRestrict i' V).flip.paste_horiz sq
  have : IsIso (idealPullbackMap i (i ∣_ U) U.ι (i ⁻¹ᵁ U).ι
      (morphismRestrict_ι i U).symm) := idealPullbackMap_open_isIso i U
  have hNew : IsIso (idealPullbackMap i (i' ∣_ V) ((f ∣_ U) ≫ U.ι)
      (gU ≫ (i ⁻¹ᵁ U).ι) sqNew.w) :=
    idealPullbackMap_comp_isIso i (i ∣_ U) (i' ∣_ V) U.ι (f ∣_ U)
      (i ⁻¹ᵁ U).ι gU (morphismRestrict_ι i U).symm sqU.w sqNew.w
  have : IsIso (idealPullbackMap i (i' ∣_ V) (V.ι ≫ f) ((i' ⁻¹ᵁ V).ι ≫ g) sqOld.w) :=
    (idealPullbackMap_isIso_congr i (i' ∣_ V) (V.ι ≫ f) ((f ∣_ U) ≫ U.ι)
      (morphismRestrict_ι f U).symm ((i' ⁻¹ᵁ V).ι ≫ g)
      (gU ≫ (i ⁻¹ᵁ U).ι) sqOld.w sqNew.w).mpr hNew
  have : IsIso (idealPullbackMap i' (i' ∣_ V) V.ι (i' ⁻¹ᵁ V).ι
      (morphismRestrict_ι i' V).symm) := idealPullbackMap_open_isIso i' V
  exact ⟨V, hx, idealPullbackMap_map_isIso_of_comp i i' (i' ∣_ V) f V.ι g
    (i' ⁻¹ᵁ V).ι sq.w (morphismRestrict_ι i' V).symm sqOld.w⟩


end AlgebraicGeometry.Conormal
