import HodgeLean.Foundations.Program.G32Native.PairedC3ResidueRatioKernel
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # The full section-space model, retaining its holomorphic summand -/

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native
variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {s : ℕ}

/-- Retained ratio equations on the full section-space model; the
holomorphic summand is kept, rather than replaced by the selected slice. -/
def pairedC3FullRatioEquations (t : Fin s → K) :
    (W × pencilResidueSpace K (s + 1)) →ₗ[K] (Fin s → K) :=
  (pairedC3RetainedRatioEquations t).comp (LinearMap.snd K W _)

/-- The kernel in the full section-space model keeps the entire
holomorphic summand and one free residue per marked pair.
Source: Schoen, Compositio Mathematica 65 (1988), proof of Lemma 2.4,
linear equations on the full fixed Abel fibre. -/
def pairedC3FullRatioKernelEquiv (t : Fin s → K) :
    LinearMap.ker (pairedC3FullRatioEquations (W := W) t) ≃ₗ[K]
      W × ((Fin s → K) × K) :=
  (show LinearMap.ker (pairedC3FullRatioEquations (W := W) t) ≃ₗ[K]
      W × LinearMap.ker (pairedC3RetainedRatioEquations t) from
    { toFun := fun v => (v.val.1, ⟨v.val.2, v.property⟩)
      invFun := fun v => ⟨(v.1, v.2.val), v.2.property⟩
      left_inv := fun v => by apply Subtype.ext; rfl
      right_inv := fun v => rfl
      map_add' := fun v w => rfl
      map_smul' := fun c v => rfl }).trans
    ((LinearEquiv.refl K W).prodCongr (pairedC3ResidueRatioKernelEquiv t))

/-- The rank here includes the holomorphic directions. -/
theorem paired_c3_full_ratio_kernel_finrank [Module.Finite K W] (t : Fin s → K) :
    Module.finrank K (LinearMap.ker (pairedC3FullRatioEquations (W := W) t)) =
      Module.finrank K W + (s + 1) := by
  rw [(pairedC3FullRatioKernelEquiv (W := W) t).finrank_eq,
    Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun,
    Module.finrank_self]

#print axioms pairedC3FullRatioEquations
#print axioms pairedC3FullRatioKernelEquiv
#print axioms paired_c3_full_ratio_kernel_finrank
end HodgeLean.Foundations.Program.G32Native
