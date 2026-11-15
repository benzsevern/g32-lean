import HodgeLean.Foundations.Program.G32Native.AffinePointFibreTensor

/-! # Normalization of the affine pullback comparison on original section values -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual affine pullback comparison carries the adjunction-unit section
value to one tensor the original section. -/
theorem affinePullbackTensor_unit (R : CommRingCat.{0}) (ε : R ⟶ CommRingCat.of ℂ)
    (N : ModuleCat R) (m : N) :
    letI : Algebra R ℂ := ε.hom.toAlgebra
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((s2e_affine_pullback_tilde_iso R (CommRingCat.of ℂ) ε).hom.app N)
      ((s2e_affine_pushforward_sections_iso R (CommRingCat.of ℂ) ε).hom.app
        ((Scheme.Modules.pullback (Spec.map ε)).obj (tilde N))
        (((moduleSpecΓFunctor (R := R)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ε)).unit.app (tilde N)))
          ((tilde.toTildeΓNatIso (R := R)).hom.app N m))) =
      (tilde.toTildeΓNatIso (R := CommRingCat.of ℂ)).hom.app
        ((ModuleCat.extendScalars ε.hom).obj N) ((1 : ℂ) ⊗ₜ[R] m) := by
  letI : Algebra R ℂ := ε.hom.toAlgebra
  let a := (tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ε))
  let b := (ModuleCat.extendRestrictScalarsAdj ε.hom).comp
    (tilde.adjunction (R := CommRingCat.of ℂ))
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (a.ofNatIsoRight (s2e_affine_pushforward_sections_iso R (CommRingCat.of ℂ) ε)) b N
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  change (tilde.adjunction (R := R)).homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ε)).homEquiv _ _
        ((s2e_affine_pullback_tilde_iso R (CommRingCat.of ℂ) ε).hom.app N)) ≫
      (s2e_affine_pushforward_sections_iso R (CommRingCat.of ℂ) ε).hom.app
        ((tilde.functor (CommRingCat.of ℂ)).obj ((ModuleCat.extendScalars ε.hom).obj N)) =
      b.unit.app N at h
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit] at h
  dsimp only [b] at h
  rw [Adjunction.comp_unit_app] at h
  exact congrArg (fun f => f m) h

#print axioms affinePullbackTensor_unit
end HodgeLean.Foundations.Program.G32Native
