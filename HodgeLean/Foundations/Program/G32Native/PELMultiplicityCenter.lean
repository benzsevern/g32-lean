import HodgeLean.Foundations.Program.G32Native.PELSkewFormCentralizer
import HodgeLean.Foundations.Abdulali.SpecialOrthogonalExteriorFixed

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations.Abdulali

/-- Tensoring endomorphisms with the marked two-dimensional identity is faithful. -/
theorem pel_lTensor_two_injective {U : Type*} [AddCommGroup U] [Module ℂ U] :
    Function.Injective (fun T : Module.End ℂ U => T.lTensor (Fin 2 → ℂ)) := by
  intro T S h
  ext u
  have he := LinearMap.congr_fun h ((Pi.single 0 1 : Fin 2 → ℂ) ⊗ₜ[ℂ] u)
  have he' := congrArg (fun w => TensorProduct.lid ℂ U
    (((LinearMap.proj 0 : (Fin 2 → ℂ) →ₗ[ℂ] ℂ).rTensor U) w)) he
  simpa using he'

/-- A skew-centralizer with the retained rank-three orthogonal multiplicity
normal form has zero Lie centre. -/
theorem pel_multiplicity_center_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : Submodule ℂ (Module.End ℂ V))
    (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] V)
    (B : LinearMap.BilinForm ℂ (Fin 6 → ℂ))
    (hs : B.IsSymm) (hnd : B.Nondegenerate)
    (normal : ∀ X : Module.End ℂ V, X ∈ L ↔
      ∃! T : Module.End ℂ (Fin 6 → ℂ),
        (∀ u v, B (T u) v + B u (T v) = 0) ∧
        e.symm.conj X = T.lTensor (Fin 2 → ℂ))
    (J : Module.End ℂ V) (hJ : J ∈ L)
    (hc : ∀ X ∈ L, J * X = X * J) : J = 0 := by
  obtain ⟨T, ⟨hT, heT⟩, _⟩ := (normal J).mp hJ
  have hTc (Y : Module.End ℂ (Fin 6 → ℂ))
      (hY : ∀ u v, B (Y u) v + B u (Y v) = 0) : T * Y = Y * T := by
    let X := e.conj (Y.lTensor (Fin 2 → ℂ))
    have heX : e.symm.conj X = Y.lTensor (Fin 2 → ℂ) := by simp [X]
    have hX : X ∈ L := by
      apply (normal X).mpr
      refine ⟨Y, ⟨hY, heX⟩, ?_⟩
      intro Z hZ
      apply pel_lTensor_two_injective
      exact hZ.2.symm.trans heX
    have hh := congrArg e.symm.conj (hc X hX)
    change e.symm.conj (J.comp X) = e.symm.conj (X.comp J) at hh
    rw [LinearEquiv.conj_comp, LinearEquiv.conj_comp, heT, heX] at hh
    change T.lTensor (Fin 2 → ℂ) * Y.lTensor (Fin 2 → ℂ) =
      Y.lTensor (Fin 2 → ℂ) * T.lTensor (Fin 2 → ℂ) at hh
    rw [← LinearMap.lTensor_mul, ← LinearMap.lTensor_mul] at hh
    exact pel_lTensor_two_injective hh
  obtain ⟨b, hb⟩ := symmetric_bilinear_orthonormal_basis B hnd hs
  have hdim : Module.finrank ℂ (Fin 6 → ℂ) = 6 := by simp
  let b6 : Module.Basis (Fin 6) ℂ (Fin 6 → ℂ) := b.reindex (finCongr hdim)
  have hb6 : LinearMap.toMatrix₂ b6 b6 B = 1 := by
    ext i j
    have hh := congrArg (fun M => M ((finCongr hdim).symm i) ((finCongr hdim).symm j)) hb
    simpa [b6, LinearMap.toMatrix₂_apply, Matrix.one_apply] using hh
  have hT0 := pel_skew_form_center_eq_zero b6 B hb6 (by decide) T hT hTc 0
  apply e.symm.conj.injective
  rw [heT, hT0, LinearMap.lTensor_zero, map_zero]

#print axioms pel_lTensor_two_injective
#print axioms pel_multiplicity_center_eq_zero
end HodgeLean.Foundations.Program.GeneralTypeIII
