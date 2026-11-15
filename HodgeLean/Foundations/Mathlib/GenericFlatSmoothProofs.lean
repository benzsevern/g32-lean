import HodgeLean.Foundations.Mathlib.GenericFlatSmoothDefs
import HodgeLean.Foundations.Mathlib.GenericSmoothFibre
import HodgeLean.Foundations.Mathlib.GenericFreeness
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Generic flatness and generic smoothness: proofs of the frozen statements -/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- Flatness of a finite type piece over a basic open, from flatness of the localized module. -/
theorem gfs_flat_appLE_basicOpen (f : X ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V) {U : X.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) (b : Γ(Y, V))
    (h : letI := (f.appLE V U e).hom.toAlgebra
      Module.Flat Γ(Y, V) (LocalizedModule (Submonoid.powers b) Γ(X, U))) :
    (f.appLE (Y.basicOpen b) (X.basicOpen (f.appLE V U e b))
      (by rw [Scheme.basicOpen_appLE]; exact inf_le_right)).hom.Flat := by
  let _ : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  set b' := f.appLE V U e b
  let _ : Algebra Γ(Y, Y.basicOpen b) Γ(X, X.basicOpen b') :=
    (f.appLE (Y.basicOpen b) (X.basicOpen b')
      (by rw [Scheme.basicOpen_appLE]; exact inf_le_right)).hom.toAlgebra
  let _ : Algebra Γ(Y, V) Γ(X, X.basicOpen b') :=
    (f.appLE V U e ≫ X.presheaf.map (homOfLE (X.basicOpen_le b')).op).hom.toAlgebra
  have : IsScalarTower Γ(Y, V) Γ(X, U) Γ(X, X.basicOpen b') :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(Y, V) Γ(Y, Y.basicOpen b) Γ(X, X.basicOpen b') :=
    .of_algebraMap_eq fun x ↦ by
      change _ = (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op ≫ f.appLE _ _ _) x
      rw [Scheme.Hom.map_appLE]
      change (f.appLE V U e ≫ X.presheaf.map (homOfLE (X.basicOpen_le b')).op) x = _
      rw [Scheme.Hom.appLE_map]
  have := hV.isLocalization_basicOpen b
  have : IsLocalization.Away (algebraMap Γ(Y, V) Γ(X, U) b) Γ(X, X.basicOpen b') :=
    hU.isLocalization_basicOpen b'
  exact HodgeLean.GenericFreeness.flat_localization_of_flat_localizedModule b h

theorem gfs_exists_flat_over_dense_open_aux (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsIntegral Y] [IsLocallyNoetherian Y] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ Flat (f ∣_ U) := by
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  obtain ⟨V, hV, hyV, -⟩ :=
    (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) (Opens.mem_top y)
  have hV : IsAffineOpen V := hV
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  -- a finite affine cover of `f ⁻¹ᵁ V`
  let ι := {U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ V}
  have hcpt : IsCompact (f ⁻¹ᵁ V : Set X) :=
    QuasiCompact.isCompact_preimage _ V.isOpen hV.isCompact
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover (fun U : ι ↦ (U.1.1 : Set X))
    (fun U ↦ U.1.1.isOpen) (by
      intro x hx
      obtain ⟨U, hU, hxU, hUle⟩ :=
        (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ f ⁻¹ᵁ V from hx)
      exact Set.mem_iUnion.mpr ⟨⟨⟨U, hU⟩, hUle⟩, hxU⟩)
  -- generic flatness on each piece of the cover
  have key : ∀ U : ι, ∃ a : Γ(Y, V), a ≠ 0 ∧ ∀ b : Γ(Y, V), a ∣ b →
      (f.appLE (Y.basicOpen b) (X.basicOpen (f.appLE V U.1.1 U.2 b))
        (by rw [Scheme.basicOpen_appLE]; exact inf_le_right)).hom.Flat := by
    intro U
    let _ : Algebra Γ(Y, V) Γ(X, U.1.1) := (f.appLE V U.1.1 U.2).hom.toAlgebra
    have : Algebra.FiniteType Γ(Y, V) Γ(X, U.1.1) :=
      HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨V, hV⟩ U.1 U.2
    obtain ⟨a, ha, h⟩ := HodgeLean.GenericFreeness.genFlat_of_finiteType
      (A := Γ(Y, V)) (B := Γ(X, U.1.1))
    exact ⟨a, ha, fun b hb ↦ gfs_flat_appLE_basicOpen f hV U.1.2 U.2 b (h b hb)⟩
  choose a ha hflat using key
  let c : Γ(Y, V) := ∏ U ∈ t, a U
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun U _ ↦ ha U
  refine ⟨Y.basicOpen c, ?_, ?_⟩
  · refine (Y.basicOpen c).isOpen.dense ?_
    rw [Set.nonempty_iff_ne_empty]
    intro h
    apply hc
    rw [← basicOpen_eq_bot_iff]
    exact SetLike.coe_injective (h.trans Opens.coe_bot.symm)
  · refine Flat.of_stalkMap _ fun x ↦ ?_
    have hx : x.1 ∈ f ⁻¹ᵁ Y.basicOpen c := x.2
    have hxV : x.1 ∈ f ⁻¹ᵁ V := Y.basicOpen_le c hx
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht hxV)
    have hle : X.basicOpen (f.appLE V U.1.1 U.2 c) ≤ f ⁻¹ᵁ Y.basicOpen c := by
      rw [Scheme.basicOpen_appLE]; exact inf_le_right
    have hxU' : x.1 ∈ X.basicOpen (f.appLE V U.1.1 U.2 c) := by
      rw [Scheme.basicOpen_appLE]; exact ⟨hxU, hx⟩
    have : IsAffine (X.basicOpen (f.appLE V U.1.1 U.2 c)) := U.1.2.basicOpen _
    have : IsAffine (Y.basicOpen c) := hV.basicOpen c
    have hg : Flat (f.resLE (Y.basicOpen c) _ hle) :=
      HasRingHomProperty.iff_of_isAffine.mpr
        ((RingHom.Flat.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f _ _ hle)).mpr
          (hflat U c (Finset.dvd_prod_of_mem a hUt)))
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff (morphismRestrictStalkMap f _ x ≪≫
      (Scheme.Hom.resLEStalkMap f hle ⟨x.1, hxU'⟩).symm)).mpr (Flat.stalkMap _ _)

theorem gfs_genericPoint_mem_smoothLocus_aux
    {k : Type u} [Field k] [CharZero k]
    (sX : X ⟶ Spec ↧k) (sY : Y ⟶ Spec ↧k) (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [LocallyOfFinitePresentation f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX]
    (hf : f ≫ sY = sX) [IsDominant f] :
    genericPoint X ∈ f.smoothLocus :=
  gfs_mem_smoothLocus_of_map_eq_genericPoint sX sY f hf _ (gfs_map_genericPoint f)

theorem gfs_genericFiber_subset_smoothLocus_aux
    {k : Type u} [Field k] [CharZero k]
    (sX : X ⟶ Spec ↧k) (sY : Y ⟶ Spec ↧k) (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX]
    (hf : f ≫ sY = sX) [IsDominant f] :
    ∀ x : X, f x = genericPoint Y → x ∈ f.smoothLocus :=
  gfs_mem_smoothLocus_of_map_eq_genericPoint sX sY f hf

/-- In a space where `p` lies in every nonempty open set, a constructible set contains or misses
an open neighbourhood of `p`. -/
private lemma gfs_constructible_open_nhd {T : Type*} [TopologicalSpace T] (p : T)
    (hp : ∀ W : Set T, IsOpen W → W.Nonempty → p ∈ W) {s : Set T}
    (hs : Topology.IsConstructible s) :
    ∃ W : Set T, IsOpen W ∧ p ∈ W ∧ (W ⊆ s ∨ Disjoint W s) := by
  induction hs using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact V hV _ =>
    by_cases hpV : p ∈ V
    · exact ⟨V, hV, hpV, .inl subset_rfl⟩
    · refine ⟨Set.univ, isOpen_univ, Set.mem_univ p, .inr ?_⟩
      rw [Set.univ_disjoint, Set.eq_empty_iff_forall_notMem]
      exact fun x hx ↦ hpV (hp V hV ⟨x, hx⟩)
  | union s _ t _ hs' ht' =>
    obtain ⟨W, hW, hpW, hWs | hWs⟩ := hs'
    · exact ⟨W, hW, hpW, .inl (hWs.trans Set.subset_union_left)⟩
    obtain ⟨W', hW', hpW', hWt | hWt⟩ := ht'
    · exact ⟨W', hW', hpW', .inl (hWt.trans Set.subset_union_right)⟩
    · exact ⟨W ∩ W', hW.inter hW', ⟨hpW, hpW'⟩, .inr (Set.disjoint_union_right.mpr
        ⟨hWs.mono_left Set.inter_subset_left, hWt.mono_left Set.inter_subset_right⟩)⟩
  | compl s _ hs' =>
    obtain ⟨W, hW, hpW, hWs | hWs⟩ := hs'
    · exact ⟨W, hW, hpW, .inr (Set.disjoint_compl_right_iff_subset.mpr hWs)⟩
    · exact ⟨W, hW, hpW, .inl (Set.subset_compl_iff_disjoint_right.mpr hWs)⟩

/-- A dense locally constructible set contains every point lying in all nonempty open sets. -/
private lemma gfs_mem_of_dense_of_isLocallyConstructible {T : Type*} [TopologicalSpace T] (p : T)
    (hp : ∀ W : Set T, IsOpen W → W.Nonempty → p ∈ W) {s : Set T}
    (hs : Topology.IsLocallyConstructible s) (hd : closure s = Set.univ) : p ∈ s := by
  obtain ⟨V, hVp, hV, hVs⟩ := hs p
  have hpV : p ∈ V := mem_of_mem_nhds hVp
  obtain ⟨W, hW, hpW, hWs | hWs⟩ := gfs_constructible_open_nhd (T := V) ⟨p, hpV⟩
    (fun W hW ⟨x, hx⟩ ↦ by
      have h := hp _ (hV.isOpenMap_subtype_val W hW) ⟨x, x, hx, rfl⟩
      obtain ⟨y, hy, hyp⟩ := h
      exact (show y = ⟨p, hpV⟩ from Subtype.ext hyp) ▸ hy) hVs
  · exact hWs hpW
  · exfalso
    have hWo : IsOpen (Subtype.val '' W) := hV.isOpenMap_subtype_val W hW
    obtain ⟨y, hyW, hys⟩ := (dense_iff_closure_eq.mpr hd).inter_open_nonempty _ hWo
      ⟨p, ⟨p, hpV⟩, hpW, rfl⟩
    obtain ⟨z, hzW, rfl⟩ := hyW
    exact Set.disjoint_left.mp hWs hzW hys

/-- An open subset of a scheme of locally finite type over a field is locally constructible. -/
private lemma gfs_isLocallyConstructible_compl_of_isOpen {k : Type u} [Field k]
    (sX : X ⟶ Spec ↧k) [LocallyOfFiniteType sX] {O : Set X} (hO : IsOpen O) :
    Topology.IsLocallyConstructible Oᶜ := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  intro x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
  refine ⟨V, V.2.mem_nhds hxV, V.2, ?_⟩
  rw [Set.preimage_compl]
  refine Topology.IsConstructible.compl (IsRetrocompact.isConstructible
    (hO.preimage continuous_subtype_val) fun U _ _ ↦ @NoetherianSpace.isCompact _ _ this _)

theorem gfs_nonsmoothLocus_not_dense_over_target_aux
    {k : Type u} [Field k] [CharZero k]
    (sX : X ⟶ Spec ↧k) (sY : Y ⟶ Spec ↧k) (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX]
    (hf : f ≫ sY = sX) [IsDominant f] :
    closure (f '' ((f.smoothLocus : Set X)ᶜ)) ≠ Set.univ := by
  intro hd
  have hc : Topology.IsLocallyConstructible (f '' ((f.smoothLocus : Set X)ᶜ)) :=
    f.isLocallyConstructible_image
      (gfs_isLocallyConstructible_compl_of_isOpen sX f.smoothLocus.2)
  have hη := gfs_mem_of_dense_of_isLocallyConstructible (genericPoint Y)
    (fun W hW hne ↦ ((genericPoint_spec Y).mem_open_set_iff hW).mpr (by simpa using hne)) hc hd
  obtain ⟨x, hxZ, hx⟩ := hη
  exact hxZ (gfs_genericFiber_subset_smoothLocus_aux sX sY f hf x hx)

theorem gfs_exists_smooth_over_dense_open_aux
    {k : Type u} [Field k] [CharZero k]
    (sX : X ⟶ Spec ↧k) (sY : Y ⟶ Spec ↧k) (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX]
    (hf : f ≫ sY = sX) [IsDominant f] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ Smooth (f ∣_ U) := by
  set C := closure (f '' ((f.smoothLocus : Set X)ᶜ))
  refine ⟨⟨Cᶜ, isClosed_closure.isOpen_compl⟩, ?_, ?_⟩
  · refine IsOpen.dense isClosed_closure.isOpen_compl ?_
    show (Cᶜ).Nonempty
    rw [Set.nonempty_compl]
    exact gfs_nonsmoothLocus_not_dense_over_target_aux sX sY f hf
  · rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
    rintro x -
    rw [Scheme.Hom.mem_smoothLocus, ← RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap f _ x).symm]
    by_contra hx
    have hxU : f x.1 ∈ Cᶜ := x.2
    exact hxU (subset_closure ⟨x.1, hx, rfl⟩)

end AlgebraicGeometry
