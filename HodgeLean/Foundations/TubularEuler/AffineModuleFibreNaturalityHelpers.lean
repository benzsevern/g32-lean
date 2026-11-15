import HodgeLean.Foundations.TubularEuler.AffineModuleFibreHelpers

/-! # Naturality of the original affine module fibre comparison

The fixed affine comparison respects the specified module morphism before specializing sections.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program

theorem affineModuleFibreIso_naturality
    (R : CommRingCat.{0}) (ψ : R ⟶ CommRingCat.of ℂ)
    (M N : (Spec R).Modules) [IsIso M.fromTildeΓ] [IsIso N.fromTildeΓ] (f : M ⟶ N) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullback (Spec.map ψ)).map f) ≫ (affineModuleFibreIso R ψ N).hom =
      (affineModuleFibreIso R ψ M).hom ≫
        (ModuleCat.extendScalars ψ.hom).map ((moduleSpecΓFunctor (R := R)).map f) := by
  let P := Scheme.Modules.pullback (Spec.map ψ)
  let F := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let Γ := moduleSpecΓFunctor (R := R)
  let S := ModuleCat.extendScalars ψ.hom
  let e := s2e_affine_pullback_tilde_iso R (CommRingCat.of ℂ) ψ
  have hc := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality f
  change (tilde.functor R).map (Γ.map f) ≫ N.fromTildeΓ = M.fromTildeΓ ≫ f at hc
  have hi : f ≫ inv N.fromTildeΓ = inv M.fromTildeΓ ≫ (tilde.functor R).map (Γ.map f) := by
    apply (cancel_epi M.fromTildeΓ).1
    rw [← Category.assoc, ← hc]
    simp only [Category.assoc, IsIso.hom_inv_id, IsIso.hom_inv_id_assoc, Category.comp_id]
  have he := e.hom.naturality (Γ.map f)
  change P.map ((tilde.functor R).map (Γ.map f)) ≫ e.hom.app (Γ.obj N) =
    e.hom.app (Γ.obj M) ≫ (tilde.functor (CommRingCat.of ℂ)).map (S.map (Γ.map f)) at he
  have ht := (tilde.toTildeΓNatIso (R := CommRingCat.of ℂ)).inv.naturality (S.map (Γ.map f))
  calc
    _ = F.map (P.map (f ≫ inv N.fromTildeΓ) ≫ e.hom.app (Γ.obj N)) ≫
        (tilde.isoTop (S.obj (Γ.obj N))).inv := by
      simp only [affineModuleFibreIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        Functor.map_comp, asIso_inv, Category.assoc, P, F, Γ, S, e]
      rfl
    _ = F.map (P.map (inv M.fromTildeΓ) ≫
        (P.map ((tilde.functor R).map (Γ.map f)) ≫ e.hom.app (Γ.obj N))) ≫
        (tilde.isoTop (S.obj (Γ.obj N))).inv := by
      rw [hi]
      simp only [Functor.map_comp, Category.assoc]
    _ = F.map (P.map (inv M.fromTildeΓ) ≫
        (e.hom.app (Γ.obj M) ≫ (tilde.functor (CommRingCat.of ℂ)).map (S.map (Γ.map f)))) ≫
        (tilde.isoTop (S.obj (Γ.obj N))).inv := by rw [he]
    _ = _ := by
      simp only [affineModuleFibreIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        Functor.map_comp, asIso_inv, Category.assoc, P, F, Γ, S, e]
      change _ ≫ _ ≫ ((F.map ((tilde.functor (CommRingCat.of ℂ)).map (S.map (Γ.map f)))) ≫
        (tilde.isoTop (S.obj (Γ.obj N))).inv) = _
      rw [show F.map ((tilde.functor (CommRingCat.of ℂ)).map (S.map (Γ.map f))) ≫
          (tilde.isoTop (S.obj (Γ.obj N))).inv =
          (tilde.isoTop (S.obj (Γ.obj M))).inv ≫ S.map (Γ.map f) from ht]
      rfl

#print axioms affineModuleFibreIso_naturality

theorem affine_pullback_tilde_unit_square
    (R : CommRingCat.{0}) (ψ : R ⟶ CommRingCat.of ℂ) (M : ModuleCat R) :
    let a := (tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ))
    let b := (ModuleCat.extendRestrictScalarsAdj ψ.hom).comp
      (tilde.adjunction (R := CommRingCat.of ℂ))
    (a.ofNatIsoRight (s2e_affine_pushforward_sections_iso R (CommRingCat.of ℂ) ψ)).unit.app M ≫
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ) ⋙ ModuleCat.restrictScalars ψ.hom).map
        ((s2e_affine_pullback_tilde_iso R (CommRingCat.of ℂ) ψ).hom.app M) = b.unit.app M := by
  exact Adjunction.unit_leftAdjointUniq_hom_app _ _ M

#print axioms affine_pullback_tilde_unit_square

end HodgeLean.Foundations.TubularEuler
