import HodgeLean.Foundations.Program.SchoenTowerI1aOpenLocalization

/-! # Affine-target descent for invariant charts
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Invariant maps to affine schemes descend through the section equalizer.
Source: SGA 1, Exposé V, §1, affine categorical quotients. -/
theorem s2v_i1alo_affine_target
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (T : Scheme) [IsAffine T] (f : U.toScheme ⟶ T)
    (hf : ∀ g, (a g).left.resLE U U (hiU g) ≫ f = f) :
    ∃! v : Spec ↧(s2v_i1a_chartInvariants X G a U hiU) ⟶ T, s2v_i1a_affineQuotientMap X G a U hiU ≫ v = f := by
  let A := s2v_i1a_chartInvariants X G a U hiU
  let c := f.appTop ≫ U.topIso.hom
  have hc (r : Γ(T, ⊤)) : c.hom r ∈ A := by
    intro g
    have hh := congrArg (fun m : U.toScheme ⟶ T => m.appTop ≫ U.topIso.hom) (hf g)
    change (f.appTop ≫ ((a g).left.resLE U U _).app ⊤) ≫ U.topIso.hom = c at hh
    rw [Scheme.Hom.resLE_app_top] at hh
    erw [Category.assoc, Category.assoc, Category.assoc, U.topIso.inv_hom_id, Category.comp_id] at hh
    exact congrArg (fun k : Γ(T, ⊤) ⟶ Γ(X.left, U) => k.hom r) hh
  let cA : Γ(T, ⊤) →+* A := c.hom.codRestrict A hc
  let v : Spec ↧A ⟶ T := Spec.map (CommRingCat.ofHom cA) ≫ T.isoSpec.inv
  have hv : s2v_i1a_affineQuotientMap X G a U hiU ≫ v = f := by
    apply (cancel_mono T.isoSpec.hom).mp
    simp only [v, s2v_i1a_affineQuotientMap, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, ← Spec.map_comp]
    change U.toSpecΓ ≫ Spec.map c = f ≫ T.toSpecΓ
    simp only [c, Scheme.Opens.toSpecΓ, Category.assoc, ← Spec.map_comp]
    simp only [Iso.hom_inv_id, Category.comp_id, Scheme.toSpecΓ_naturality]
  refine ⟨v, hv, ?_⟩
  intro v' hv'
  apply eq_of_SpecMap_comp_eq_of_isAffineOpen (CommRingCat.ofHom A.subtype)
    Subtype.val_injective ⊤ (isAffineOpen_top _) (by simp) (by simp)
  apply (cancel_epi hU.isoSpec.hom).mp
  exact hv'.trans hv.symm

end HodgeLean.Foundations.Program
