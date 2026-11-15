import HodgeLean.Foundations.Program.SchoenCycleStep1FixedField
import HodgeLean.Foundations.Program.SchoenCycleStep1Quotient

/-! # Fixed-field normalization using the retained original normalization
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The original-field deck square determines the actual rational pullback.
Source: Mathlib, faithfulness of Spec and the generic-point monomorphism. -/
theorem s2v_i2a_field_deck_eq_rational_pullback
    (W : Scheme) [IsIntegral W] (d : W ⟶ W) [IsIso d]
    (δ : W.functionField ≃+* W.functionField)
    (hδ : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ W.fromSpecStalk (genericPoint W) =
      W.fromSpecStalk (genericPoint W) ≫ d) :
    δ.toRingHom = s2e_step1_fieldPullback W d := by
  have H : CommRingCat.ofHom δ.toRingHom =
      CommRingCat.ofHom (s2e_step1_fieldPullback W d) := by
    apply Quiver.Hom.op_inj
    apply Scheme.Spec.map_injective
    change Spec.map (CommRingCat.ofHom δ.toRingHom) =
      Spec.map (CommRingCat.ofHom (s2e_step1_fieldPullback W d))
    apply (cancel_mono (W.fromSpecStalk (genericPoint W))).mp
    exact hδ.trans (s2e_step1_fieldPullback_generic W d).symm
  exact congrArg CommRingCat.Hom.hom H

/-- A fixed-subfield normalization of the retained categorical quotient has its actual projection as an isomorphism.
Source: Mathlib, Scheme.Hom.normalizationDesc; the reduced invariant-factor criterion for categorical quotients. -/
theorem s2v_i2a_fixed_subfield_normalization_isIso
    (W B : Over (Spec ↧ℂ)) [IsIntegral W.left]
    (β : W ⟶ B) [IsFinite β.left]
    (d : W ⟶ W) (hd : d ≫ β = β)
    (hcat : ∀ (T : Over (Spec ↧ℂ)) (f : W ⟶ T), d ≫ f = f →
      ∃! u : B ⟶ T, β ≫ u = f)
    (η : Spec W.left.functionField ⟶ B.left) [QuasiCompact η] [QuasiSeparated η]
    (e : η.normalization ≅ W.left)
    (he : e.hom ≫ β.left = η.fromNormalization)
    (hgeneric : η.toNormalization ≫ e.hom = W.left.fromSpecStalk (genericPoint W.left))
    (δ : W.left.functionField ≃+* W.left.functionField)
    (hδ : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
      W.left.fromSpecStalk (genericPoint W.left) =
        W.left.fromSpecStalk (genericPoint W.left) ≫ d.left)
    (L : Subfield W.left.functionField) (hL : ∀ z : L, δ z = z)
    (θ : Spec (CommRingCat.of L) ⟶ B.left) [QuasiCompact θ] [QuasiSeparated θ]
    (hθ : Spec.map (CommRingCat.ofHom L.subtype) ≫ θ = η) :
    IsIso θ.fromNormalization := by
  let κ : CommRingCat.of L ⟶ W.left.functionField := CommRingCat.ofHom L.subtype
  let v : Spec W.left.functionField ⟶ θ.normalization := Spec.map κ ≫ θ.toNormalization
  have hv : η = v ≫ θ.fromNormalization := by
    dsimp only [v]
    rw [Category.assoc, θ.toNormalization_fromNormalization, hθ]
  let g : W.left ⟶ θ.normalization :=
    e.inv ≫ η.normalizationDesc v θ.fromNormalization hv
  have hg : g ≫ θ.fromNormalization = β.left := by
    dsimp only [g]
    rw [Category.assoc, Scheme.Hom.normalizationDesc_comp, ← he,
      ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hgen : W.left.fromSpecStalk (genericPoint W.left) ≫ g = v := by
    rw [← hgeneric]
    dsimp only [g]
    rw [Category.assoc, ← Category.assoc e.hom, e.hom_inv_id, Category.id_comp,
      Scheme.Hom.toNormalization_normalizationDesc]
  haveI : IsFinite (g ≫ θ.fromNormalization) := by rw [hg]; infer_instance
  haveI : IsFinite g := IsFinite.of_comp g θ.fromNormalization
  haveI : Surjective (Spec.map κ) := by
    constructor
    change Function.Surjective (PrimeSpectrum.comap κ.hom)
    intro x
    exact ⟨default, Subsingleton.elim _ _⟩
  haveI : IsDominant (W.left.fromSpecStalk (genericPoint W.left) ≫ g) := by
    rw [hgen]
    dsimp only [v]
    infer_instance
  haveI : IsDominant g := IsDominant.of_comp
    (W.left.fromSpecStalk (genericPoint W.left)) g
  haveI : Surjective g := surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range
  have hginv : d.left ≫ g = g := by
    haveI : IsDominant (W.left.fromSpecStalk (genericPoint W.left)) :=
      s2e_step1_generic_dominant W.left
    apply ext_of_isDominant_of_isSeparated θ.fromNormalization (ι :=
      W.left.fromSpecStalk (genericPoint W.left))
    · rw [Category.assoc, hg]
      exact congrArg Over.Hom.left hd
    · rw [← Category.assoc, ← hδ, Category.assoc, hgen]
      change Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ (Spec.map κ ≫ θ.toNormalization) =
        Spec.map κ ≫ θ.toNormalization
      have hκ : κ ≫ CommRingCat.ofHom δ.toRingHom = κ := by
        ext z
        exact hL z
      rw [← Category.assoc, ← Spec.map_comp, hκ]
  let T : Over (Spec ↧ℂ) := Over.mk (θ.fromNormalization ≫ B.hom)
  let p : T ⟶ B := Over.homMk θ.fromNormalization
  let f : W ⟶ T := Over.homMk g (by
    change g ≫ (θ.fromNormalization ≫ B.hom) = W.hom
    rw [← Category.assoc, hg]
    exact Over.w β)
  haveI : Surjective f.left := inferInstanceAs (Surjective g)
  haveI : IsReduced T.left := by
    change IsReduced θ.normalization
    infer_instance
  haveI : IsSeparated p.left := inferInstanceAs (IsSeparated θ.fromNormalization)
  exact s2e_step1_quotient_reduced_factor_isIso W B T Unit (fun _ => d) β
    (fun _ => hd) (fun U f hf => hcat U f (hf ())) f p
    (fun _ => by apply Over.OverMorphism.ext; exact hginv)
    (by apply Over.OverMorphism.ext; exact hg)

/-- The actual fixed rational subfield recovers a categorical quotient whose original normalization is retained.
Source: Mathlib, normalizationDesc and the checked fixed-rational-field generic map. -/
theorem s2v_i2a_retained_fixed_field_normalization
    (W B : Over (Spec ↧ℂ)) [IsIntegral W.left]
    (β : W ⟶ B) [IsFinite β.left]
    (d : W ⟶ W) [IsIso d] (hd : d ≫ β = β)
    (hcat : ∀ (T : Over (Spec ↧ℂ)) (f : W ⟶ T), d ≫ f = f →
      ∃! u : B ⟶ T, β ≫ u = f)
    (η : Spec W.left.functionField ⟶ B.left) [QuasiCompact η] [QuasiSeparated η]
    (e : η.normalization ≅ W.left)
    (he : e.hom ≫ β.left = η.fromNormalization)
    (hgeneric : η.toNormalization ≫ e.hom = W.left.fromSpecStalk (genericPoint W.left))
    (δ : W.left.functionField ≃+* W.left.functionField)
    (hδ : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
      W.left.fromSpecStalk (genericPoint W.left) =
        W.left.fromSpecStalk (genericPoint W.left) ≫ d.left)
    (U : B.left.Opens) (hU : IsAffineOpen U) [Nonempty (β.left ⁻¹ᵁ U)] :
    let L := s2e_step1_fixedField W.left Unit (fun _ => d.left)
    ∃ (θ : Spec (CommRingCat.of L) ⟶ B.left) (hθaff : IsAffineHom θ),
      letI := hθaff
      Spec.map (CommRingCat.ofHom L.subtype) ≫ θ = η ∧ IsIso θ.fromNormalization := by
  intro L
  obtain ⟨θ, hθaff, hθ⟩ := s2e_step1_fixedField_genericMap W.left B.left Unit
    (fun _ => d.left) β.left (fun _ => congrArg Over.Hom.left hd) U hU
  letI := hθaff
  have hη : W.left.fromSpecStalk (genericPoint W.left) ≫ β.left = η := by
    rw [← hgeneric, Category.assoc, he, η.toNormalization_fromNormalization]
  have hθ' : Spec.map (CommRingCat.ofHom L.subtype) ≫ θ = η := hθ.trans hη
  have hδring : δ.toRingHom = s2e_step1_fieldPullback W.left d.left :=
    s2v_i2a_field_deck_eq_rational_pullback W.left d.left δ hδ
  have hL (z : L) : δ z = z := by
    have H := (s2e_step1_mem_fixedField W.left Unit (fun _ => d.left) z.val).mp z.property ()
    change δ.toRingHom z.val = z.val
    rw [hδring]
    exact H
  refine ⟨θ, hθaff, hθ', ?_⟩
  exact s2v_i2a_fixed_subfield_normalization_isIso W B β d hd hcat η e he hgeneric
    δ hδ L hL θ hθ'

end HodgeLean.Foundations.Program
