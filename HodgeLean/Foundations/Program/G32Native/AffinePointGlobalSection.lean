import HodgeLean.Foundations.Program.G32Native.AffinePointSpecialization
import HodgeLean.Foundations.Program.G32Native.ModuleSectionValueUnit

/-! # Actual global section morphisms in the affine point-fibre comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- The affine point adjunction specializes an original global section morphism
by its actual pullback on the inverse image of the point's structure-module unit. -/
theorem affinePointUnit_globalSection (R : CommRingCat.{0}) (ε : R ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) (s : unit (Spec R) ⟶ M) :
    (s2e_affine_pushforward_sections_iso R (CommRingCat.of ℂ) ε).hom.app
      ((Scheme.Modules.pullback (Spec.map ε)).obj M)
      (((moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ε)).unit.app M))
        (s.val.app (op ⊤) (1 : Γ(Spec R, ⊤)))) =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullback (Spec.map ε)).map s)
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit (Spec.map ε)).inv
          (1 : Γ(Spec ↧ℂ, ⊤))) := by
  let L := Scheme.Modules.pullback (Spec.map ε)
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ε)
  let u := (s2e_affine_pushforward_sections_iso R (CommRingCat.of ℂ) ε).hom.app
    (L.obj (unit (Spec R)))
    (((moduleSpecΓFunctor (R := R)).map (adj.unit.app (unit (Spec R))))
      (1 : Γ(Spec R, ⊤)))
  have hu := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (Spec.map ε).toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at hu
  have hv := congrArg (fun f => f.val.app (op ⊤) (1 : Γ(Spec R, ⊤))) hu
  change (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit (Spec.map ε)).hom u =
    (Spec.map ε).appTop (1 : Γ(Spec R, ⊤)) at hv
  rw [map_one] at hv
  let e := ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    (pullbackUnit (Spec.map ε))).toLinearEquiv
  have hunit : u = e.symm (1 : Γ(Spec ↧ℂ, ⊤)) :=
    (e.symm_apply_eq.mpr hv.symm).symm
  have hn := congrArg (fun f => f.val.app (op ⊤) (1 : Γ(Spec R, ⊤)))
    (adj.unit.naturality s)
  change (s2e_affine_pushforward_sections_iso R (CommRingCat.of ℂ) ε).hom.app
      (L.obj M) (((moduleSpecΓFunctor (R := R)).map (adj.unit.app M))
        (s.val.app (op ⊤) (1 : Γ(Spec R, ⊤)))) =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (L.map s) u at hn
  rw [hunit] at hn
  exact hn

/-- The actual pullback of an original global section morphism is one tensor
its original global section under the affine point-fibre comparison. -/
theorem affinePointFibreTensorEquiv_globalSection
    (R : CommRingCat.{0}) (ε : R ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ] (s : unit (Spec R) ⟶ M) :
    letI : Algebra R ℂ := ε.hom.toAlgebra
    affinePointFibreTensorEquiv R ε M
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullback (Spec.map ε)).map s)
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit (Spec.map ε)).inv
          (1 : Γ(Spec ↧ℂ, ⊤)))) =
      (1 : ℂ) ⊗ₜ[R] (show (moduleSpecΓFunctor (R := R)).obj M from
        s.val.app (op ⊤) (1 : Γ(Spec R, ⊤))) := by
  rw [← affinePointUnit_globalSection, affinePointFibreTensorEquiv_unit]

/-- The affine dual comparison preserves the evaluation of every actual
global section morphism, including its original point pullback. -/
theorem affinePointDualEquiv_globalSection
    (R : CommRingCat.{0}) (ε : R ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ] (s : unit (Spec R) ⟶ M)
    (ν : Module.Dual ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map ε)).obj M))) :
    letI : Algebra R ℂ := ε.hom.toAlgebra
    affinePointDualEquiv R ε M ν
      (show (moduleSpecΓFunctor (R := R)).obj M from
        s.val.app (op ⊤) (1 : Γ(Spec R, ⊤))) =
      ν ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullback (Spec.map ε)).map s)
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit (Spec.map ε)).inv
          (1 : Γ(Spec ↧ℂ, ⊤)))) := by
  letI : Algebra R ℂ := ε.hom.toAlgebra
  change ν ((affinePointFibreTensorEquiv R ε M).symm
    ((1 : ℂ) ⊗ₜ[R] (show (moduleSpecΓFunctor (R := R)).obj M from
      s.val.app (op ⊤) (1 : Γ(Spec R, ⊤))))) = _
  apply congrArg ν
  apply (affinePointFibreTensorEquiv R ε M).symm_apply_eq.mpr
  exact (affinePointFibreTensorEquiv_globalSection R ε M s).symm

#print axioms affinePointDualEquiv_globalSection
#print axioms affinePointFibreTensorEquiv_globalSection
#print axioms affinePointUnit_globalSection
end HodgeLean.Foundations.Program.G32Native
