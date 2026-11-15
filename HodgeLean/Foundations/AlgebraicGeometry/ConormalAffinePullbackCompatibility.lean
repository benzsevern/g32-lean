import HodgeLean.Foundations.Program.SchoenCycleC2AffinePullbackHelpers

/-! # Adjunction compatibility of affine scalar extension
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program

namespace AlgebraicGeometry.Conormal

/-- The isomorphism between two left adjoints respects transposition. -/
lemma leftAdjointUniq_homEquiv_comp
    {C D : Type*} [Category C] [Category D] {F F' : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G) (X : C) (Y : D) (u : F'.obj X ⟶ Y) :
    a.homEquiv X Y ((Adjunction.leftAdjointUniq a b).hom.app X ≫ u) =
      b.homEquiv X Y u := by
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

/-- Affine pullback and scalar extension give the same transpose on global sections. -/
lemma affinePullbackTilde_transpose
    (R S : CommRingCat.{0}) (f : R ⟶ S) (M : ModuleCat R) (N : (Spec S).Modules)
    (u : (ModuleCat.extendScalars f.hom).obj M ⟶ (moduleSpecΓFunctor (R := S)).obj N) :
    (tilde.adjunction (R := R)).homEquiv _ _
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).homEquiv _ _
          ((s2e_affine_pullback_tilde_iso R S f).hom.app M ≫
            ((tilde.adjunction (R := S)).homEquiv _ _).symm u)) ≫
        (s2e_affine_pushforward_sections_iso R S f).hom.app N =
      (ModuleCat.extendRestrictScalarsAdj f.hom).homEquiv _ _ u := by
  let a := ((tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).ofNatIsoRight
      (s2e_affine_pushforward_sections_iso R S f)
  let b := (ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S))
  have ht := leftAdjointUniq_homEquiv_comp a b M N
    (((tilde.adjunction (R := S)).homEquiv _ _).symm u)
  change _ = (ModuleCat.extendRestrictScalarsAdj f.hom).homEquiv _ _
    ((tilde.adjunction (R := S)).homEquiv _ _
      (((tilde.adjunction (R := S)).homEquiv _ _).symm u)) at ht
  rw [Equiv.apply_symm_apply] at ht
  exact ht

end AlgebraicGeometry.Conormal
