import HodgeLean.Foundations.Program.G32Native.AffinePullbackTensorUnit

/-! # The affine tensor model retains actual point specialization -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- In the actual affine point fibre, the original adjunction-unit section
specialization is one tensor the original section under the tensor comparison. -/
theorem affinePointFibreTensorEquiv_unit
    (R : CommRingCat.{0}) (ε : R ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ]
    (m : (moduleSpecΓFunctor (R := R)).obj M) :
    letI : Algebra R ℂ := ε.hom.toAlgebra
    affinePointFibreTensorEquiv R ε M
      ((s2e_affine_pushforward_sections_iso R (CommRingCat.of ℂ) ε).hom.app
        ((Scheme.Modules.pullback (Spec.map ε)).obj M)
        (((moduleSpecΓFunctor (R := R)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ε)).unit.app M)) m)) =
      (1 : ℂ) ⊗ₜ[R] m := by
  letI : Algebra R ℂ := ε.hom.toAlgebra
  let N := (moduleSpecΓFunctor (R := R)).obj M
  let L := Scheme.Modules.pullback (Spec.map ε)
  let eL := ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    (L.mapIso (asIso M.fromTildeΓ))).toLinearEquiv
  let uM := (s2e_affine_pushforward_sections_iso R (CommRingCat.of ℂ) ε).hom.app (L.obj M)
    (((moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ε)).unit.app M)) m)
  let uN := (s2e_affine_pushforward_sections_iso R (CommRingCat.of ℂ) ε).hom.app (L.obj (tilde N))
    (((moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ε)).unit.app (tilde N)))
      ((tilde.toTildeΓNatIso (R := R)).hom.app N m))
  have ht : (moduleSpecΓFunctor (R := R)).map M.fromTildeΓ
      ((tilde.toTildeΓNatIso (R := R)).hom.app N m) = m :=
    congrArg (fun f => f m) ((tilde.adjunction (R := R)).right_triangle_components M)
  have hn := congrArg
    (fun f : tilde N ⟶ (Scheme.Modules.pushforward (Spec.map ε)).obj (L.obj M) =>
      (moduleSpecΓFunctor (R := R)).map f
        ((tilde.toTildeΓNatIso (R := R)).hom.app N m))
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ε)).unit.naturality M.fromTildeΓ)
  change (moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ε)).unit.app M)
      ((moduleSpecΓFunctor (R := R)).map M.fromTildeΓ
        ((tilde.toTildeΓNatIso (R := R)).hom.app N m)) = eL uN at hn
  rw [ht] at hn
  have hp : eL.symm uM = uN := eL.symm_apply_eq.mpr hn
  change ((tilde.toTildeΓNatIso (R := CommRingCat.of ℂ)).app
      ((ModuleCat.extendScalars ε.hom).obj N)).symm.toLinearEquiv
    ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((s2e_affine_pullback_tilde_iso R (CommRingCat.of ℂ) ε).hom.app N)
      (eL.symm uM)) = _
  rw [hp]
  change ((tilde.toTildeΓNatIso (R := CommRingCat.of ℂ)).app
      ((ModuleCat.extendScalars ε.hom).obj N)).symm.toLinearEquiv
    ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((s2e_affine_pullback_tilde_iso R (CommRingCat.of ℂ) ε).hom.app N)
      ((s2e_affine_pushforward_sections_iso R (CommRingCat.of ℂ) ε).hom.app
        (L.obj (tilde N))
        (((moduleSpecΓFunctor (R := R)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ε)).unit.app (tilde N)))
          ((tilde.toTildeΓNatIso (R := R)).hom.app N m)))) = _
  rw [affinePullbackTensor_unit]
  exact (((tilde.toTildeΓNatIso (R := CommRingCat.of ℂ)).app
    ((ModuleCat.extendScalars ε.hom).obj N)).toLinearEquiv).symm_apply_apply _

#print axioms affinePointFibreTensorEquiv_unit
end HodgeLean.Foundations.Program.G32Native
