import HodgeLean.Foundations.Program.SchoenTowerI1aDescentHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_restrict_invariant
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U V : X.left.Opens) (hUV : U ≤ V)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V)
    (r : s2v_i1a_chartInvariants X G a V hiV) :
    (X.left.presheaf.map (homOfLE hUV).op).hom r.val ∈
      s2v_i1a_chartInvariants X G a U hiU := by
  intro g
  have he : X.left.presheaf.map (homOfLE hUV).op ≫ (a g).left.appLE U U (hiU g) =
      (a g).left.appLE V V (hiV g) ≫ X.left.presheaf.map (homOfLE hUV).op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  have he' := congrArg (fun k : Γ(X.left, V) ⟶ Γ(X.left, U) => k.hom r.val) he
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, r.property g] using he'

/-- Restriction of actual invariant sections on nested preserved opens.
Source: SGA 1, Exposé V, §1, restriction of invariant affine charts. -/
def s2v_i1ahi_invariantRestriction
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U V : X.left.Opens) (hUV : U ≤ V)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V) :
    CommRingCat.of (s2v_i1a_chartInvariants X G a V hiV) ⟶
      CommRingCat.of (s2v_i1a_chartInvariants X G a U hiU) :=
  CommRingCat.ofHom (((X.left.presheaf.map (homOfLE hUV).op).hom.comp
    (s2v_i1a_chartInvariants X G a V hiV).subtype).codRestrict
      (s2v_i1a_chartInvariants X G a U hiU)
      (s2v_i1ahi_restrict_invariant X G a U V hUV hiU hiV))

example (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U V : X.left.Opens) (hUV : U ≤ V)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V) :
    s2v_i1ahi_invariantRestriction X G a U V hUV hiU hiV ≫
      CommRingCat.ofHom (s2v_i1a_chartInvariants X G a U hiU).subtype =
    CommRingCat.ofHom (s2v_i1a_chartInvariants X G a V hiV).subtype ≫
      X.left.presheaf.map (homOfLE hUV).op := rfl

lemma s2v_i1ahi_transition_square
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U V : X.left.Opens) (hUV : U ≤ V)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V) :
    s2v_i1a_affineQuotientMap X G a U hiU ≫
      Spec.map (s2v_i1ahi_invariantRestriction X G a U V hUV hiU hiV) =
    X.left.homOfLE hUV ≫ s2v_i1a_affineQuotientMap X G a V hiV := by
  have he : s2v_i1ahi_invariantRestriction X G a U V hUV hiU hiV ≫
      CommRingCat.ofHom (s2v_i1a_chartInvariants X G a U hiU).subtype =
    CommRingCat.ofHom (s2v_i1a_chartInvariants X G a V hiV).subtype ≫
      X.left.presheaf.map (homOfLE hUV).op := rfl
  dsimp only [s2v_i1a_affineQuotientMap]
  rw [Category.assoc, ← Spec.map_comp, he, Spec.map_comp, ← Category.assoc,
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map]
  rfl

lemma s2v_i1ahi_transition_unique
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U V : X.left.Opens) (hU : IsAffineOpen U) (hUV : U ≤ V)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V) :
    ∃! j : Spec ↧(s2v_i1a_chartInvariants X G a U hiU) ⟶
      Spec ↧(s2v_i1a_chartInvariants X G a V hiV),
      s2v_i1a_affineQuotientMap X G a U hiU ≫ j =
        X.left.homOfLE hUV ≫ s2v_i1a_affineQuotientMap X G a V hiV := by
  refine ⟨Spec.map (s2v_i1ahi_invariantRestriction X G a U V hUV hiU hiV),
    s2v_i1ahi_transition_square X G a U V hUV hiU hiV, fun j hj => ?_⟩
  haveI : IsIso U.toSpecΓ := by change IsIso hU.isoSpec.hom; infer_instance
  apply s2v_i1ahi_cancel_invariant_spectrum
    (s2v_i1a_chartInvariants X G a U hiU)
    (Spec ↧(s2v_i1a_chartInvariants X G a V hiV)) j
  apply (cancel_epi U.toSpecΓ).mp
  exact hj.trans (s2v_i1ahi_transition_square X G a U V hUV hiU hiV).symm

lemma s2v_i1ahi_invariantRestriction_comp
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U V W : X.left.Opens) (hUV : U ≤ V) (hVW : V ≤ W)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (hiV : ∀ g, V ≤ (a g).left ⁻¹ᵁ V)
    (hiW : ∀ g, W ≤ (a g).left ⁻¹ᵁ W) :
    s2v_i1ahi_invariantRestriction X G a V W hVW hiV hiW ≫
      s2v_i1ahi_invariantRestriction X G a U V hUV hiU hiV =
    s2v_i1ahi_invariantRestriction X G a U W (hUV.trans hVW) hiU hiW := by
  have he : X.left.presheaf.map (homOfLE hVW).op ≫
      X.left.presheaf.map (homOfLE hUV).op =
      X.left.presheaf.map (homOfLE (hUV.trans hVW)).op := by
    rw [← Functor.map_comp]
    rfl
  ext r
  exact congrArg (fun k : Γ(X.left, W) ⟶ Γ(X.left, U) => k.hom r.val) he

end HodgeLean.Foundations.Program
