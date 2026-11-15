import HodgeLean.Foundations.Program.G32Native.PairedC3AffineConormalTensor
import HodgeLean.Foundations.Program.G32Native.PairedC3SurjectiveKernelTensor
import HodgeLean.Foundations.Program.SchoenCycleC2ScalarExtensionTensorHelpers

/-! # Specified affine conormal bases from original kernel classes -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The native extension-of-scalars comparison preserves each original unit tensor. -/
theorem paired_c3_extend_scalars_tensor_unit
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (M : ModuleCat R) (x : M) :
    (s2e_extendScalars_algebraMap_iso (S := S) M).hom
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.app M x) =
      (1 : S) ⊗ₜ[R] x := by
  let S₀ := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  letI : Module S S₀ := inferInstanceAs (Module S S)
  letI : IsScalarTower R S S₀ := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  unfold s2e_extendScalars_algebraMap_iso
  erw [TensorProduct.AlgebraTensorModule.congr_tmul]
  rfl

/-- A specified ring-kernel cotangent basis gives a basis of actual affine
conormal global sections through the natural comparison. -/
def pairedC3AffineConormalBasis (R S : CommRingCat.{0}) (p : R ⟶ S)
    (hp : Function.Surjective p) {σ : Type}
    (b : Module.Basis σ (R ⧸ RingHom.ker p.hom) (RingHom.ker p.hom).Cotangent) :
    Module.Basis σ S ((moduleSpecΓFunctor (R := S)).obj (Conormal.sheaf (Spec.map p))) := by
  letI := p.hom.toAlgebra
  let T := (ModuleCat.extendScalars p.hom).obj (ModuleCat.of R (RingHom.ker p.hom))
  let E := s2e_extendScalars_algebraMap_iso (S := S) (ModuleCat.of R (RingHom.ker p.hom))
  let C := (moduleSpecΓFunctor (R := S)).mapIso (pairedC3AffineConormalTensorIso R S p) ≪≫
    (tilde.toTildeΓNatIso.app T).symm
  exact ((pairedC3SurjectiveKernelTensorBasis p.hom hp b).map E.symm.toLinearEquiv).map
    C.symm.toLinearEquiv

/-- Every labelled affine basis section is its original canonical conormal class. -/
theorem paired_c3_affine_conormal_basis_apply (R S : CommRingCat.{0}) (p : R ⟶ S)
    (hp : Function.Surjective p) {σ : Type}
    (b : Module.Basis σ (R ⧸ RingHom.ker p.hom) (RingHom.ker p.hom).Cotangent)
    (x : σ → RingHom.ker p.hom)
    (hb : ∀ a, b a = (RingHom.ker p.hom).toCotangent (x a))
    (s : σ → (moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule (Spec.map p)))
    (hs : ∀ a, s2e_affine_ideal_sections_equiv R S p (s a) = x a) (a : σ) :
    pairedC3AffineConormalBasis R S p hp b a =
      pairedC3PullbackSection (Spec.map p) (Conormal.idealModule (Spec.map p)) ⊤ (s a) := by
  letI := p.hom.toAlgebra
  let K := ModuleCat.of R (RingHom.ker p.hom)
  let T := (ModuleCat.extendScalars p.hom).obj K
  let E := s2e_extendScalars_algebraMap_iso (S := S) K
  let C := (moduleSpecΓFunctor (R := S)).mapIso (pairedC3AffineConormalTensorIso R S p) ≪≫
    (tilde.toTildeΓNatIso.app T).symm
  change C.symm.toLinearEquiv (E.symm.toLinearEquiv (pairedC3SurjectiveKernelTensorBasis p.hom hp b a)) = _
  apply C.toLinearEquiv.injective
  change C.hom (C.inv _) = _
  rw [Iso.inv_hom_id_apply]
  have hg := paired_c3_affine_conormal_tensor_generator R S p (s a)
  have hgc := congrArg ((tilde.toTildeΓNatIso.app T).inv) hg
  change C.hom (pairedC3PullbackSection (Spec.map p)
    (Conormal.idealModule (Spec.map p)) ⊤ (s a)) =
      (tilde.toTildeΓNatIso.app T).inv ((tilde.toTildeΓNatIso.app T).hom
        ((ModuleCat.extendRestrictScalarsAdj p.hom).unit.app K
          (s2e_affine_ideal_sections_equiv R S p (s a)))) at hgc
  rw [Iso.hom_inv_id_apply] at hgc
  change E.inv _ = C.hom _
  rw [hgc, hs a]
  apply E.toLinearEquiv.injective
  change E.hom (E.inv _) = _
  rw [Iso.inv_hom_id_apply, paired_c3_surjective_kernel_tensor_basis_apply p.hom hp b x hb]
  exact (paired_c3_extend_scalars_tensor_unit (S := S) K (x a)).symm

#print axioms paired_c3_affine_conormal_basis_apply
end HodgeLean.Foundations.Program.G32Native
