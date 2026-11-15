import HodgeLean.Foundations.Program.G32Native.UnionConormalIdealEpiAffineTarget

/-! # Global epic ideal comparison in cartesian immersion diagrams -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Natural ideal comparison in a cartesian square of immersions is epic. -/
lemma unionConormal_idealMap_epi_of_isPullback
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (f : W' ⟶ W) (g : Q' ⟶ Q) (sq : IsPullback g i' i f) :
    Epi (idealPullbackMap i i' f g sq.w) := by
  apply unionConormal_epi_of_open_neighborhoods
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
  have hLocal : Epi (idealPullbackMap (i ∣_ U) (i' ∣_ V) (f ∣_ U) gU sqU.w) :=
    unionConormal_idealMap_epi_of_affine_target (i ∣_ U) (i' ∣_ V) (f ∣_ U) gU sqU
  have sqNew : IsPullback (gU ≫ (i ⁻¹ᵁ U).ι) (i' ∣_ V) i ((f ∣_ U) ≫ U.ι) :=
    sqU.paste_horiz (isPullback_morphismRestrict i U).flip
  have sqOld : IsPullback ((i' ⁻¹ᵁ V).ι ≫ g) (i' ∣_ V) i (V.ι ≫ f) :=
    (isPullback_morphismRestrict i' V).flip.paste_horiz sq
  have : IsIso (idealPullbackMap i (i ∣_ U) U.ι (i ⁻¹ᵁ U).ι
      (morphismRestrict_ι i U).symm) := idealPullbackMap_open_isIso i U
  have hNew : Epi (idealPullbackMap i (i' ∣_ V) ((f ∣_ U) ≫ U.ι)
      (gU ≫ (i ⁻¹ᵁ U).ι) sqNew.w) :=
    unionConormal_idealMap_comp_epi i (i ∣_ U) (i' ∣_ V) U.ι (f ∣_ U)
      (i ⁻¹ᵁ U).ι gU (morphismRestrict_ι i U).symm sqU.w sqNew.w
  have : Epi (idealPullbackMap i (i' ∣_ V) (V.ι ≫ f) ((i' ⁻¹ᵁ V).ι ≫ g) sqOld.w) :=
    unionConormal_idealMap_epi_congr i (i' ∣_ V) ((f ∣_ U) ≫ U.ι) (V.ι ≫ f)
      (morphismRestrict_ι f U) (gU ≫ (i ⁻¹ᵁ U).ι) ((i' ⁻¹ᵁ V).ι ≫ g) sqNew.w sqOld.w
  have : IsIso (idealPullbackMap i' (i' ∣_ V) V.ι (i' ⁻¹ᵁ V).ι
      (morphismRestrict_ι i' V).symm) := idealPullbackMap_open_isIso i' V
  haveI := unionConormal_idealMap_map_epi_of_comp i i' (i' ∣_ V) f V.ι g
    (i' ⁻¹ᵁ V).ι sq.w (morphismRestrict_ι i' V).symm sqOld.w
  exact ⟨V, hx, unionConormal_epi_map_of_natIso
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm
    (idealPullbackMap i i' f g sq.w)⟩

end HodgeLean.Foundations.Program.G32Native
