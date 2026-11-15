import HodgeLean.Foundations.TubularEuler.AffineModuleFibreNaturalityHelpers

/-! # The original affine point pullback unit on module sections

The canonical unit precedes comparison with scalar extension.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program

def affineModulePointUnit (R : CommRingCat.{0}) (ψ : R ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) :
    (moduleSpecΓFunctor (R := R)).obj M ⟶
      (ModuleCat.restrictScalars ψ.hom).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
          ((Scheme.Modules.pullback (Spec.map ψ)).obj M)) :=
  (moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ)).unit.app M) ≫
    (s2e_affine_pushforward_sections_iso R (CommRingCat.of ℂ) ψ).hom.app
      ((Scheme.Modules.pullback (Spec.map ψ)).obj M)

theorem affineModulePointUnit_naturality
    (R : CommRingCat.{0}) (ψ : R ⟶ CommRingCat.of ℂ)
    (M N : (Spec R).Modules) (f : M ⟶ N) :
    (moduleSpecΓFunctor (R := R)).map f ≫ affineModulePointUnit R ψ N =
      affineModulePointUnit R ψ M ≫
        (ModuleCat.restrictScalars ψ.hom).map
          ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
            ((Scheme.Modules.pullback (Spec.map ψ)).map f)) := by
  let P := Scheme.Modules.pullback (Spec.map ψ)
  let G := Scheme.Modules.pushforward (Spec.map ψ)
  let Γ := moduleSpecΓFunctor (R := R)
  let F := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let S := ModuleCat.restrictScalars ψ.hom
  let η := (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ)).unit
  let θ := s2e_affine_pushforward_sections_iso R (CommRingCat.of ℂ) ψ
  have hη := η.naturality f
  change f ≫ η.app N = η.app M ≫ G.map (P.map f) at hη
  have hθ := θ.hom.naturality (P.map f)
  change Γ.map (G.map (P.map f)) ≫ θ.hom.app (P.obj N) =
    θ.hom.app (P.obj M) ≫ S.map (F.map (P.map f)) at hθ
  change Γ.map f ≫ (Γ.map (η.app N) ≫ θ.hom.app (P.obj N)) =
    (Γ.map (η.app M) ≫ θ.hom.app (P.obj M)) ≫ S.map (F.map (P.map f))
  rw [← Category.assoc, ← Functor.map_comp, hη, Functor.map_comp, Category.assoc, hθ,
    Category.assoc]

#print axioms affineModulePointUnit_naturality

theorem affineModulePointUnit_tilde_square
    (R : CommRingCat.{0}) (ψ : R ⟶ CommRingCat.of ℂ) (M : ModuleCat R) :
    (tilde.adjunction (R := R)).unit.app M ≫
      affineModulePointUnit R ψ ((tilde.functor R).obj M) ≫
        (ModuleCat.restrictScalars ψ.hom).map
          ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
            ((s2e_affine_pullback_tilde_iso R (CommRingCat.of ℂ) ψ).hom.app M)) =
      (ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app M ≫
        (ModuleCat.restrictScalars ψ.hom).map
          ((tilde.adjunction (R := CommRingCat.of ℂ)).unit.app
            ((ModuleCat.extendScalars ψ.hom).obj M)) := by
  simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Category.assoc,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj, affineModulePointUnit] using affine_pullback_tilde_unit_square R ψ M

#print axioms affineModulePointUnit_tilde_square

end HodgeLean.Foundations.TubularEuler
