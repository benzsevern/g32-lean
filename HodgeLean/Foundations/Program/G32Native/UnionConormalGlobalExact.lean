import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineExactRecognition
import HodgeLean.Foundations.Program.G32Native.UnionConormalOpenFirstArrow
import HodgeLean.Foundations.Program.G32Native.UnionConormalOpenLastObject
import HodgeLean.Foundations.Program.G32Native.UnionConormalResLEClosed
import HodgeLean.Foundations.Program.G32Native.UnionConormalLastEpi
import HodgeLean.Foundations.Program.G32Native.UnionConormalComplex
import HodgeLean.Foundations.Program.G32Native.UnionConormalLocalExact
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Exactness of the actual union conormal complex by affine open descent -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A locally noetherian ambient scheme gives exactness of the actual natural complex. -/
lemma unionConormal_exact_of_locallyNoetherian
    {V T T₁ T₂ Z : Scheme.{0}} [IsLocallyNoetherian V]
    (t : T ⟶ V) (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    [IsClosedImmersion t] [IsClosedImmersion t₁] [IsClosedImmersion t₂]
    (a : T₁ ⟶ T) (s₁ : Z ⟶ T₁) (s₂ : Z ⟶ T₂)
    [IsClosedImmersion s₁] [IsClosedImmersion s₂]
    (ha : a ≫ t = t₁) (hs : s₁ ≫ t₁ = s₂ ≫ t₂)
    (hunion : t.ker = t₁.ker ⊓ t₂.ker)
    (hinter : (s₁ ≫ t₁).ker = t₁.ker ⊔ t₂.ker) :
    (unionConormalComplex t t₁ t₂ a s₁ s₂ ha hs hunion).Exact := by
  let K := unionConormalComplex t t₁ t₂ a s₁ s₂ ha hs hunion
  haveI : Epi K.g := unionConormalLast_epi t₁ t₂ s₁ s₂ hs hinter
  apply unionConormal_exact_of_open_neighborhoods K
  intro x
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (X := V)
    (U := ⊤) (x := t₁ x) (show t₁ x ∈ (⊤ : V.Opens) from trivial)
  let U₀ := t ⁻¹ᵁ U
  let U₁ := t₁ ⁻¹ᵁ U
  let U₂ := t₂ ⁻¹ᵁ U
  let UZ := s₁ ⁻¹ᵁ U₁
  have hA : U₁ = a ⁻¹ᵁ U₀ := by
    change t₁ ⁻¹ᵁ U = a ⁻¹ᵁ (t ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, ha]
  have hZ : UZ = s₂ ⁻¹ᵁ U₂ := by
    change s₁ ⁻¹ᵁ (t₁ ⁻¹ᵁ U) = s₂ ⁻¹ᵁ (t₂ ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hs]
  let a' := a.resLE U₀ U₁ hA.le
  let s₁' := s₁ ∣_ U₁
  let s₂' := s₂.resLE U₂ UZ hZ.le
  have hb : a' ≫ U₀.ι = U₁.ι ≫ a := a.resLE_comp_ι hA.le
  have ha' : a' ≫ (t ∣_ U) = t₁ ∣_ U := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hb,
      Category.assoc, ha, morphismRestrict_ι]
  have hu : s₁' ≫ (t₁ ∣_ U) = (s₁ ≫ t₁) ∣_ U := by
    apply (cancel_mono U.ι).mp
    change ((s₁ ∣_ U₁) ≫ (t₁ ∣_ U)) ≫ U.ι = _
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
      morphismRestrict_ι, morphismRestrict_ι, Category.assoc]
    rfl
  have hs₂sq : s₂' ≫ U₂.ι = UZ.ι ≫ s₂ := s₂.resLE_comp_ι hZ.le
  have hs' : s₁' ≫ (t₁ ∣_ U) = s₂' ≫ (t₂ ∣_ U) := by
    apply (cancel_mono U.ι).mp
    calc
      (s₁' ≫ (t₁ ∣_ U)) ≫ U.ι = UZ.ι ≫ s₁ ≫ t₁ := by
        rw [Category.assoc s₁' (t₁ ∣_ U) U.ι, morphismRestrict_ι t₁ U,
          ← Category.assoc s₁' U₁.ι t₁, morphismRestrict_ι s₁ U₁, Category.assoc]
      _ = UZ.ι ≫ s₂ ≫ t₂ := by rw [hs]
      _ = (s₂' ≫ (t₂ ∣_ U)) ≫ U.ι := by
        rw [Category.assoc s₂' (t₂ ∣_ U) U.ι, morphismRestrict_ι t₂ U,
          ← Category.assoc s₂' U₂.ι t₂, hs₂sq, Category.assoc]
  have hinter' : (s₁' ≫ (t₁ ∣_ U)).ker = (t₁ ∣_ U).ker ⊔ (t₂ ∣_ U).ker := by
    rw [hu]
    exact unionConormal_restrict_kernel_sup (s₁ ≫ t₁) t₁ t₂ hinter U
  haveI : IsAffine U.toScheme := hU
  haveI : IsAffine U₀.toScheme := hU.preimage t
  haveI : IsAffine U₁.toScheme := hU.preimage t₁
  haveI : IsAffine U₂.toScheme := hU.preimage t₂
  haveI : IsAffine UZ.toScheme := (hU.preimage t₁).preimage s₁
  haveI : IsClosedImmersion s₂' := unionConormal_resLE_isClosedImmersion s₂ U₂ UZ hZ.le hZ
  haveI : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.toScheme⟩
  let R := Scheme.Modules.restrictFunctor U₁.ι
  let F := Scheme.Modules.pullback U₁.toScheme.isoSpec.inv
  haveI := unionConormal_isoPullback_isEquivalence U₁.toScheme.isoSpec.inv
  letI := (Scheme.Modules.restrictAdjunction U₁.ι).leftAdjoint_preservesColimits
  letI := (Scheme.Modules.pullbackPushforwardAdjunction U₁.toScheme.isoSpec.inv).leftAdjoint_preservesColimits
  haveI : Epi ((K.map R).map F).g := by change Epi (F.map (R.map K.g)); infer_instance
  have he := unionConormal_affine_exact_recognition (t ∣_ U) (t₁ ∣_ U) (t₂ ∣_ U)
    a' s₁' s₂' ha' hs' (unionConormal_restrict_kernel_inf t t₁ t₂ hunion U) hinter'
    ((K.map R).map F)
    (F.mapArrow.mapIso (unionConormalOpenFirstArrowIso t t₁ a ha U a' ha' hb))
    (F.mapIso (unionConormalOpenLastObjectIso s₁ s₂ U₁ U₂ hZ.le hZ))
  exact ⟨U₁, hx, ((K.map R).exact_map_iff_of_faithful F).mp he⟩

end HodgeLean.Foundations.Program.G32Native
