import HodgeLean.Adapters.NormalConeB4aGysinAffineFibre

/-! # Affine parameter charts of a flat scheme family

The structure map on an affine open supplies a flat polynomial algebra.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry

/-- An affine open of a flat scheme family has a compatible flat polynomial structure map. -/
theorem a3b4a_gysin_affineOpen_parameter_chart
    {k : Type} [Field k] {K : Scheme.{0}} (h : K ⟶ a3b2_line k) [Flat h]
    (U : K.Opens) (hU : IsAffineOpen U) :
    ∃ φ : Polynomial k →+* Γ(K, U),
      hU.isoSpec.inv ≫ U.ι ≫ h = Spec.map (CommRingCat.ofHom φ) ∧ φ.Flat := by
  let f := hU.isoSpec.inv ≫ U.ι ≫ h
  let φ : Polynomial k →+* Γ(K, U) := (Spec.preimage f).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = f := Spec.map_preimage f
  refine ⟨φ, hφ.symm, ?_⟩
  have hf : Flat f := by dsimp only [f]; infer_instance
  rw [← hφ] at hf
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp hf


/-- The fibre over an affine parameter chart is its parameter quotient spectrum,
compatibly with the inclusion into that chart. -/
theorem a3b4a_gysin_affineOpen_fibre_chart
    {k : Type} [Field k] {K : Scheme.{0}} (h : K ⟶ a3b2_line k)
    (U : K.Opens) (hU : IsAffineOpen U) [Algebra (Polynomial k) Γ(K, U)]
    (hmap : hU.isoSpec.inv ≫ U.ι ≫ h =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) Γ(K, U)))) (s : k) :
    ∃ e : ((pullback.fst h (a3b2_point k s)) ⁻¹ᵁ U).toScheme ≅
      Spec (CommRingCat.of (Γ(K, U) ⧸ Ideal.span
        {algebraMap (Polynomial k) Γ(K, U) (Polynomial.X - Polynomial.C s)})),
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {algebraMap (Polynomial k) Γ(K, U) (Polynomial.X - Polynomial.C s)}))) =
        (pullback.fst h (a3b2_point k s) ∣_ U) ≫ hU.isoSpec.hom := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) Γ(K, U)))
  have h1 := isPullback_morphismRestrict (pullback.fst h (a3b2_point k s)) U
  have h2 := IsPullback.of_hasPullback h (a3b2_point k s)
  have h3 := h1.paste_vert h2
  have h4 := h3.of_iso (Iso.refl _) hU.isoSpec (Iso.refl _) (Iso.refl _)
    (Category.id_comp _).symm (by simp)
    (by dsimp only [f]; rw [Iso.refl_hom, Category.comp_id, ← hmap, Iso.hom_inv_id_assoc])
    (by simp)
    (fst' := (pullback.fst h (a3b2_point k s) ∣_ U) ≫ hU.isoSpec.hom)
    (snd' := ((pullback.fst h (a3b2_point k s)) ⁻¹ᵁ U).ι ≫ pullback.snd h (a3b2_point k s))
    (f' := f) (g' := a3b2_point k s)
  have h5 := IsPullback.of_hasPullback f (a3b2_point k s)
  let e₀ := h4.isoIsPullback _ _ h5
  let e₁ := a3b4a_gysin_affineFibreIso (R := Γ(K, U)) s
  have he₁ : e₁.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span {algebraMap (Polynomial k) Γ(K, U) (Polynomial.X - Polynomial.C s)}))) =
      pullback.fst f (a3b2_point k s) := by
    rw [← a3b4a_gysin_affineFibreIso_inv_fst s, Iso.hom_inv_id_assoc]
  refine ⟨e₀ ≪≫ e₁, ?_⟩
  rw [Iso.trans_hom, Category.assoc, he₁]
  exact IsPullback.isoIsPullback_hom_fst _ _ h4 h5

end HodgeLean.Adapters
