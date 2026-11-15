import HodgeLean.Foundations.TubularEuler.AffineModulePointUnitHelpers

/-! # The canonical scalar-extension unit through the retained affine comparison

The original point pullback unit becomes the scalar-extension unit of the original module of sections.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program

theorem affineModulePointUnit_comparison
    (R : CommRingCat.{0}) (ψ : R ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ] :
    affineModulePointUnit R ψ M ≫
      (ModuleCat.restrictScalars ψ.hom).map (affineModuleFibreIso R ψ M).hom =
        (ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app
          ((moduleSpecΓFunctor (R := R)).obj M) := by
  let P := Scheme.Modules.pullback (Spec.map ψ)
  let Γ := moduleSpecΓFunctor (R := R)
  let F := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let S := ModuleCat.restrictScalars ψ.hom
  let B := ModuleCat.extendScalars ψ.hom
  let e := s2e_affine_pullback_tilde_iso R (CommRingCat.of ℂ) ψ
  let T := (tilde.functor R).obj (Γ.obj M)
  let t := tilde.isoTop (B.obj (Γ.obj M))
  have hη : Γ.map (inv M.fromTildeΓ) = (tilde.adjunction (R := R)).unit.app (Γ.obj M) := by
    apply (cancel_mono (Γ.map M.fromTildeΓ)).1
    rw [← Functor.map_comp, IsIso.inv_hom_id, Γ.map_id]
    exact ((tilde.adjunction (R := R)).right_triangle_components M).symm
  have hn := affineModulePointUnit_naturality R ψ M T (inv M.fromTildeΓ)
  have he := affineModulePointUnit_tilde_square R ψ (Γ.obj M)
  have hc : S.map (affineModuleFibreIso R ψ M).hom =
      S.map (F.map (P.map (inv M.fromTildeΓ))) ≫
        S.map (F.map (e.hom.app (Γ.obj M))) ≫ S.map t.inv := by
    simp only [affineModuleFibreIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      asIso_inv, Functor.map_comp, Category.assoc, P, Γ, F, S, B, e, t]
    rfl
  rw [hc]
  calc
    _ = (Γ.map (inv M.fromTildeΓ) ≫ affineModulePointUnit R ψ T) ≫
        S.map (F.map (e.hom.app (Γ.obj M))) ≫ S.map t.inv := by
      rw [hn]
      simp only [Category.assoc, P, Γ, F, S]
    _ = ((tilde.adjunction (R := R)).unit.app (Γ.obj M) ≫
        affineModulePointUnit R ψ T ≫ S.map (F.map (e.hom.app (Γ.obj M)))) ≫ S.map t.inv := by
      rw [hη]
      simp only [Category.assoc]
    _ = ((ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app (Γ.obj M) ≫
        S.map ((tilde.adjunction (R := CommRingCat.of ℂ)).unit.app (B.obj (Γ.obj M)))) ≫
          S.map t.inv := by
      exact congrArg (fun f => f ≫ S.map t.inv) he
    _ = _ := by
      rw [Category.assoc, ← Functor.map_comp]
      change (ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app (Γ.obj M) ≫
        S.map (t.hom ≫ t.inv) = _
      rw [Iso.hom_inv_id, S.map_id]
      ext x
      rfl

#print axioms affineModulePointUnit_comparison

theorem affineModuleFibreIso_pointUnit_apply
    (R : CommRingCat.{0}) (ψ : R ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ]
    (m : (moduleSpecΓFunctor (R := R)).obj M) :
    (affineModuleFibreIso R ψ M).hom (affineModulePointUnit R ψ M m) =
      (1 : ℂ) ⊗ₜ[R, ψ.hom] m := by
  have h := ConcreteCategory.congr_hom (affineModulePointUnit_comparison R ψ M) m
  change (affineModuleFibreIso R ψ M).hom (affineModulePointUnit R ψ M m) =
    (ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app
      ((moduleSpecΓFunctor (R := R)).obj M) m at h
  exact h.trans (ModuleCat.extendRestrictScalarsAdj_unit_app_apply ψ.hom _ m)

#print axioms affineModuleFibreIso_pointUnit_apply

end HodgeLean.Foundations.TubularEuler
