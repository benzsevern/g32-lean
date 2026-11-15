import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualRestrictionScheme
import Mathlib.AlgebraicGeometry.Gluing

/-! # Equality on affine refinements of residual quotient overlaps -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Around each residual point of an overlap, one common ambient affine
refinement with equal restrictions suffices for equality on the actual pullback. -/
theorem pairedC3_quotient_overlap_ext_of_local
    {X Y : Scheme} (I : X.IdealSheafData) (V V' : X.affineOpens)
    (f : Spec (CommRingCat.of (Γ(X, V) ⧸ I.ideal V)) ⟶ Y)
    (g : Spec (CommRingCat.of (Γ(X, V') ⧸ I.ideal V')) ⟶ Y)
    (h : ∀ x : I.subscheme, I.subschemeι x ∈ V.1 → I.subschemeι x ∈ V'.1 →
      ∃ (W : X.affineOpens) (hWV : W.1 ≤ V.1) (hWV' : W.1 ≤ V'.1),
        I.subschemeι x ∈ W.1 ∧
        Spec.map (CommRingCat.ofHom (pairedC3AffineResidualRestriction I V W hWV)) ≫ f =
        Spec.map (CommRingCat.ofHom (pairedC3AffineResidualRestriction I V' W hWV')) ≫ g) :
    pullback.fst (I.subschemeCover.f V) (I.subschemeCover.f V') ≫ f =
      pullback.snd _ _ ≫ g := by
  let p := pullback.fst (I.subschemeCover.f V) (I.subschemeCover.f V') ≫
    I.subschemeCover.f V
  let q := p ≫ I.subschemeι
  apply Scheme.hom_ext_of_forall
  intro z
  have hzV : q z ∈ V.1 := by
    have hz : p z ∈ (I.subschemeCover.f V).opensRange :=
      ⟨(pullback.fst (I.subschemeCover.f V) (I.subschemeCover.f V')) z, rfl⟩
    rwa [I.opensRange_subschemeCover_map] at hz
  have hzV' : q z ∈ V'.1 := by
    have hp : p = pullback.snd (I.subschemeCover.f V) (I.subschemeCover.f V') ≫
        I.subschemeCover.f V' := pullback.condition
    have hz : p z ∈ (I.subschemeCover.f V').opensRange := by
      rw [hp]
      exact ⟨(pullback.snd (I.subschemeCover.f V) (I.subschemeCover.f V')) z, rfl⟩
    rwa [I.opensRange_subschemeCover_map] at hz
  obtain ⟨W', hWV, hWV', hzW, heq⟩ := h (p z) hzV hzV'
  let O := q ⁻¹ᵁ W'.1
  have hr : Set.range (O.ι ≫ p) ⊆ Set.range (I.subschemeCover.f W') := by
    rintro _ ⟨x, rfl⟩
    change (O.ι ≫ p) x ∈ (I.subschemeCover.f W').opensRange
    rw [I.opensRange_subschemeCover_map]
    exact x.property
  let b := IsOpenImmersion.lift (I.subschemeCover.f W') (O.ι ≫ p) hr
  have hb : b ≫ I.subschemeCover.f W' = O.ι ≫ p := IsOpenImmersion.lift_fac _ _ _
  have hbV : b ≫ Spec.map (CommRingCat.ofHom
      (pairedC3AffineResidualRestriction I V W' hWV)) = O.ι ≫ pullback.fst _ _ := by
    apply (cancel_mono (I.subschemeCover.f V)).mp
    rw [Category.assoc, pairedC3_residual_restriction_scheme, hb, Category.assoc]
  have hbV' : b ≫ Spec.map (CommRingCat.ofHom
      (pairedC3AffineResidualRestriction I V' W' hWV')) = O.ι ≫ pullback.snd _ _ := by
    apply (cancel_mono (I.subschemeCover.f V')).mp
    rw [Category.assoc, pairedC3_residual_restriction_scheme, hb, Category.assoc]
    exact congrArg (fun m => O.ι ≫ m) (pullback.condition ..)
  refine ⟨O, hzW, ?_⟩
  rw [← Category.assoc, ← hbV, Category.assoc, heq,
    ← Category.assoc, hbV', Category.assoc]

/-- Equality after restriction to every common ambient affine neighbourhood
implies equality on the actual pullback of residual quotient charts. -/
theorem pairedC3_quotient_overlap_ext
    {X Y : Scheme} (I : X.IdealSheafData) (V V' : X.affineOpens)
    (f : Spec (CommRingCat.of (Γ(X, V) ⧸ I.ideal V)) ⟶ Y)
    (g : Spec (CommRingCat.of (Γ(X, V') ⧸ I.ideal V')) ⟶ Y)
    (h : ∀ (W : X.affineOpens) (hWV : W.1 ≤ V.1) (hWV' : W.1 ≤ V'.1),
      Spec.map (CommRingCat.ofHom (pairedC3AffineResidualRestriction I V W hWV)) ≫ f =
      Spec.map (CommRingCat.ofHom (pairedC3AffineResidualRestriction I V' W hWV')) ≫ g) :
    pullback.fst (I.subschemeCover.f V) (I.subschemeCover.f V') ≫ f =
      pullback.snd _ _ ≫ g := by
  apply pairedC3_quotient_overlap_ext_of_local I V V' f g
  intro x hxV hxV'
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show I.subschemeι x ∈ V.1 ⊓ V'.1 from ⟨hxV, hxV'⟩) (V.1 ⊓ V'.1).2
  have hWV : W ≤ V.1 := fun _ hx => (hWle hx).1
  have hWV' : W ≤ V'.1 := fun _ hx => (hWle hx).2
  exact ⟨⟨W, hW⟩, hWV, hWV', hxW, h ⟨W, hW⟩ hWV hWV'⟩

#print axioms pairedC3_quotient_overlap_ext_of_local
#print axioms pairedC3_quotient_overlap_ext
end HodgeLean.Foundations.Program.G32Native
