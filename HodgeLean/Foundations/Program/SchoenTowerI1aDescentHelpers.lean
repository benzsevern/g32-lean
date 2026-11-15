import HodgeLean.Foundations.Program.SchoenTowerI1aFiniteHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
universe u

lemma s2v_i1ahi_invariant_section_pullback
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (T : Scheme) (f : U.toScheme ⟶ T)
    (hf : ∀ g, (a g).left.resLE U U (hiU g) ≫ f = f)
    (r : Γ(T, ⊤)) :
    (f.appTop ≫ U.topIso.hom).hom r ∈ s2v_i1a_chartInvariants X G a U hiU := by
  intro g
  have he := congrArg Scheme.Hom.appTop (hf g)
  change f.appTop ≫ ((a g).left.resLE U U (hiU g)).app ⊤ = f.appTop at he
  rw [Scheme.Hom.resLE_app_top] at he
  have he' := congrArg (fun k => k ≫ U.topIso.hom) he
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at he'
  exact congrArg (fun k : Γ(T, ⊤) ⟶ Γ(X.left, U) => k.hom r) he'

/-- The actual section map of an invariant morphism with its range restricted.
Source: SGA 1, Exposé V, §1, the affine invariant-ring construction. -/
def s2v_i1ahi_invariantSectionMap
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (T : Scheme) (f : U.toScheme ⟶ T)
    (hf : ∀ g, (a g).left.resLE U U (hiU g) ≫ f = f) :
    Γ(T, ⊤) ⟶ CommRingCat.of (s2v_i1a_chartInvariants X G a U hiU) :=
  CommRingCat.ofHom ((f.appTop ≫ U.topIso.hom).hom.codRestrict
    (s2v_i1a_chartInvariants X G a U hiU)
    (s2v_i1ahi_invariant_section_pullback X G a U hiU T f hf))

example (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (T : Scheme) (f : U.toScheme ⟶ T)
    (hf : ∀ g, (a g).left.resLE U U (hiU g) ≫ f = f) :
    s2v_i1ahi_invariantSectionMap X G a U hiU T f hf ≫
      CommRingCat.ofHom (s2v_i1a_chartInvariants X G a U hiU).subtype =
        f.appTop ≫ U.topIso.hom := rfl

lemma s2v_i1ahi_cancel_invariant_spectrum
    {A : Type u} [CommRing A] (B : Subring A)
    (T : Scheme) [IsAffine T]
    (v w : Spec ↧B ⟶ T)
    (h : Spec.map (CommRingCat.ofHom B.subtype) ≫ v =
      Spec.map (CommRingCat.ofHom B.subtype) ≫ w) : v = w := by
  apply (cancel_mono T.toSpecΓ).mp
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (v ≫ T.toSpecΓ)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (w ≫ T.toSpecΓ)
  have he := congrArg (fun k => k ≫ T.toSpecΓ) h
  simp only [Category.assoc, ← hφ, ← hψ, ← Spec.map_comp] at he
  have he' := Spec.map_injective he
  have heq : φ = ψ := by
    ext r
    exact congrArg (fun k : Γ(T, ⊤) ⟶ CommRingCat.of A => k.hom r) he'
  rw [← hφ, ← hψ, heq]

lemma s2v_i1ahi_affine_factor_from_sections
    (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
    (B : Subring Γ(X, U)) (T : Scheme) [IsAffine T]
    (f : U.toScheme ⟶ T) (φ : Γ(T, ⊤) ⟶ CommRingCat.of B)
    (hφ : φ ≫ CommRingCat.ofHom B.subtype = f.appTop ≫ U.topIso.hom) :
    ∃! v : Spec ↧B ⟶ T,
      (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom B.subtype)) ≫ v = f := by
  let v := Spec.map φ ≫ T.isoSpec.inv
  have hv : (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom B.subtype)) ≫ v = f := by
    dsimp [v]
    rw [Category.assoc, ← Category.assoc (Spec.map (CommRingCat.ofHom B.subtype)),
      ← Spec.map_comp, hφ, Spec.map_comp]
    dsimp [Scheme.Opens.toSpecΓ]
    simp only [Category.assoc, ← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id,
      Category.id_comp, Category.comp_id]
    rw [← Scheme.toSpecΓ_naturality_assoc]
    change f ≫ T.isoSpec.hom ≫ T.isoSpec.inv = f
    rw [Iso.hom_inv_id, Category.comp_id]
  refine ⟨v, hv, fun w hw => ?_⟩
  haveI : IsIso U.toSpecΓ := by change IsIso hU.isoSpec.hom; infer_instance
  apply s2v_i1ahi_cancel_invariant_spectrum B T w v
  apply (cancel_epi U.toSpecΓ).mp
  simpa only [← Category.assoc] using hw.trans hv.symm

end HodgeLean.Foundations.Program
