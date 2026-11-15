import HodgeLean.Foundations.TubularEuler.ConormalFibreTensorHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2AffineIdealKernelHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ScalarExtensionTensorHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2AffinePullbackHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2IdealModuleAffineHelpers
import HodgeLean.Foundations.BundleThom.ConormalFibre

/-! # Actual affine module fibres by scalar extension

The comparison uses the original associated-module counit, affine pullback, and global sections.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleThom

def affineModuleFibreIso (R : CommRingCat.{0}) (ψ : R ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ] :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map ψ)).obj M) ≅
      (ModuleCat.extendScalars ψ.hom).obj ((moduleSpecΓFunctor (R := R)).obj M) := by
  let F := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let N := (moduleSpecΓFunctor (R := R)).obj M
  exact F.mapIso
    ((Scheme.Modules.pullback (Spec.map ψ)).mapIso (asIso M.fromTildeΓ).symm ≪≫
      (s2e_affine_pullback_tilde_iso R (CommRingCat.of ℂ) ψ).app N) ≪≫
    (tilde.isoTop (R := CommRingCat.of ℂ) ((ModuleCat.extendScalars ψ.hom).obj N)).symm

def affineCompositeModuleFibreIso
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ] :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map ψ)).obj
        ((Scheme.Modules.pullback (Spec.map φ)).obj M)) ≅
      (ModuleCat.extendScalars (φ ≫ ψ).hom).obj
        ((moduleSpecΓFunctor (R := R)).obj M) :=
  (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    ((Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).app M ≪≫
      (Scheme.Modules.pullbackCongr (Spec.map_comp φ ψ).symm).app M) ≪≫
    affineModuleFibreIso R (φ ≫ ψ) M

#print axioms affineCompositeModuleFibreIso

def affineConormalFibreIdealSectionsIso
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map ψ)).obj (Conormal.sheaf (Spec.map φ))) ≅
      (ModuleCat.extendScalars (φ ≫ ψ).hom).obj
        ((moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule (Spec.map φ))) := by
  let M := Conormal.idealModule (Spec.map φ)
  letI : IsIso M.fromTildeΓ := s2e_idealModule_spec_fromTilde_isIso R (Spec.map φ)
  exact affineCompositeModuleFibreIso R S φ ψ M

def affineConormalFibreIdealTensorIso
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ) :
    letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map ψ)).obj (Conormal.sheaf (Spec.map φ))) ≅
      ModuleCat.of ℂ (ℂ ⊗[R] RingHom.ker φ.hom) := by
  letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
  exact affineConormalFibreIdealSectionsIso R S φ ψ ≪≫
    (ModuleCat.extendScalars (φ ≫ ψ).hom).mapIso
      (s2e_affine_ideal_sections_equiv R S φ).toModuleIso ≪≫
    s2e_extendScalars_algebraMap_iso (ModuleCat.of R (RingHom.ker φ.hom))

def affineConormalFibreCotangentIso
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ) :
    letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map ψ)).obj (Conormal.sheaf (Spec.map φ))) ≅
      ModuleCat.of ℂ (ℂ ⊗[R] (RingHom.ker φ.hom).Cotangent) := by
  letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
  have hkill : ∀ r ∈ RingHom.ker φ.hom, algebraMap R ℂ r = 0 := by
    intro r hr
    change φ.hom r = 0 at hr
    change ψ.hom (φ.hom r) = 0
    rw [hr, map_zero]
  exact affineConormalFibreIdealTensorIso R S φ ψ ≪≫
    (conormalFibreTensorEquiv (RingHom.ker φ.hom) hkill).toModuleIso

def affineActualConormalFibreIso
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (q : Spec S ⟶ Spec (CommRingCat.of ℂ))
    (x : ComplexPoint (Over.mk q)) :
    letI : Algebra R ℂ := (φ ≫ Spec.preimage x.left).hom.toAlgebra
    i1_conormalFibre (Spec.map φ) x ≅
      ModuleCat.of ℂ (ℂ ⊗[R] (RingHom.ker φ.hom).Cotangent) := by
  letI : Algebra R ℂ := (φ ≫ Spec.preimage x.left).hom.toAlgebra
  exact (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    ((Scheme.Modules.pullbackCongr (Spec.map_preimage x.left).symm).app
      (Conormal.sheaf (Spec.map φ))) ≪≫
    affineConormalFibreCotangentIso R S φ (Spec.preimage x.left)

#print axioms affineActualConormalFibreIso

#print axioms affineConormalFibreCotangentIso

#print axioms affineConormalFibreIdealTensorIso

#print axioms affineConormalFibreIdealSectionsIso

#print axioms affineModuleFibreIso

end HodgeLean.Foundations.TubularEuler
