import HodgeLean.Foundations.Program.G32Native.PairedC3SemilinearBasis
import Mathlib.RingTheory.Extension.Basic

/-! # Scalar extension of an original surjective ring kernel -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The given surjection, with a set-theoretic lifting of its target elements. -/
def pairedC3SurjectiveExtension {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    letI := f.toAlgebra
    Algebra.Extension R S := by
  letI := f.toAlgebra
  exact {
    Ring := R
    σ := Function.surjInv hf
    algebraMap_σ := Function.surjInv_eq hf }

/-- The extension cotangent retains the original quotient coefficient ring. -/
def pairedC3SurjectiveCotangentEquiv {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    letI := f.toAlgebra
    let P := pairedC3SurjectiveExtension f hf
    let q := f.quotientKerEquivOfSurjective hf
    haveI := RingHomInvPair.of_ringEquiv q.symm
    haveI := RingHomInvPair.of_ringEquiv_symm q.symm
    P.Cotangent ≃ₛₗ[(q.symm : S →+* R ⧸ RingHom.ker f)] (RingHom.ker f).Cotangent := by
  letI := f.toAlgebra
  let P := pairedC3SurjectiveExtension f hf
  let q := f.quotientKerEquivOfSurjective hf
  letI := RingHomInvPair.of_ringEquiv q.symm
  letI := RingHomInvPair.of_ringEquiv_symm q.symm
  refine {
    toFun := fun x => Algebra.Extension.Cotangent.val (P := P) x
    invFun := fun x => Algebra.Extension.Cotangent.of (P := P) x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := ?_ }
  intro s x
  have hs : q.symm s = Ideal.Quotient.mk (RingHom.ker f) (Function.surjInv hf s) := by
    apply q.injective
    rw [q.apply_symm_apply]
    exact (P.algebraMap_σ s).symm
  change Function.surjInv hf s • (show (RingHom.ker f).Cotangent from x) =
    q.symm s • (show (RingHom.ker f).Cotangent from x)
  rw [hs]
  exact (IsScalarTower.algebraMap_smul (R ⧸ RingHom.ker f) (Function.surjInv hf s)
    (show (RingHom.ker f).Cotangent from x)).symm

/-- A specified cotangent basis gives a basis of the actual scalar-extended kernel. -/
def pairedC3SurjectiveKernelTensorBasis {R S ι : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (b : Module.Basis ι (R ⧸ RingHom.ker f) (RingHom.ker f).Cotangent) :
    letI := f.toAlgebra
    Module.Basis ι S (S ⊗[R] RingHom.ker f) := by
  letI := f.toAlgebra
  let P := pairedC3SurjectiveExtension f hf
  let q := f.quotientKerEquivOfSurjective hf
  letI := RingHomInvPair.of_ringEquiv q.symm
  letI := RingHomInvPair.of_ringEquiv_symm q.symm
  exact (pairedC3SemilinearBasis q.symm (pairedC3SurjectiveCotangentEquiv f hf) b).map
    P.cotangentEquiv.symm

/-- Original ideal-class basis vectors lift to their original unit tensors. -/
theorem paired_c3_surjective_kernel_tensor_basis_apply
    {R S ι : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (b : Module.Basis ι (R ⧸ RingHom.ker f) (RingHom.ker f).Cotangent)
    (x : ι → RingHom.ker f) (hb : ∀ a, b a = (RingHom.ker f).toCotangent (x a)) (a : ι) :
    letI := f.toAlgebra
    pairedC3SurjectiveKernelTensorBasis f hf b a = (1 : S) ⊗ₜ[R] x a := by
  letI := f.toAlgebra
  let P := pairedC3SurjectiveExtension f hf
  let q := f.quotientKerEquivOfSurjective hf
  letI := RingHomInvPair.of_ringEquiv q.symm
  letI := RingHomInvPair.of_ringEquiv_symm q.symm
  change P.cotangentEquiv.symm
    (pairedC3SemilinearBasis q.symm (pairedC3SurjectiveCotangentEquiv f hf) b a) = _
  rw [paired_c3_semilinear_basis_apply]
  apply P.cotangentEquiv.injective
  rw [P.cotangentEquiv.apply_symm_apply]
  erw [Algebra.Extension.cotangentEquiv_tmul, one_smul]
  apply Algebra.Extension.Cotangent.ext
  change b a = (RingHom.ker f).toCotangent (x a)
  exact hb a

#print axioms paired_c3_surjective_kernel_tensor_basis_apply
end HodgeLean.Foundations.Program.G32Native
