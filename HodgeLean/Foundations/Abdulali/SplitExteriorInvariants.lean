import HodgeLean.Foundations.Abdulali.SplitPowerCoordinates
import HodgeLean.Foundations.Abdulali.SpecialOrthogonalComparison

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- Transport of a rational Hodge Lie normal form to alternating SO-fixed tensors.
Source: Abdulali, Annals 155 (2002), §4; Borel, Linear Algebraic Groups, II.7. -/
theorem split_exterior_hodge_invariants
    {V U : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
    (e : ((Fin 2 → ℂ) ⊗[ℂ] U) ≃ₗ[ℂ] (ℂ ⊗[ℚ] V))
    (B : LinearMap.BilinForm ℂ U) (hB : B.Nondegenerate) (hs : B.IsSymm)
    (hc : ∀ X : Module.End ℂ (ℂ ⊗[ℚ] V),
      X ∈ complexSpan (hodgeLieAlgebra H hH).toSubmodule ↔
      ∃! T : Module.End ℂ U, (∀ x y, B (T x) y + B x (T y) = 0) ∧
        e.symm.conj X = T.lTensor (Fin 2 → ℂ))
    (r n : ℕ) (v : ⋀[ℂ]^n (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ)))) :
    v ∈ exteriorHodgeClasses H hH r n ↔
      exteriorEquiv n (splitPowerCoordinates r e) v ∈
        (m1b_fixed (m1b_copies (r*2) ''
          {u ∈ m1b_isometries B | u.det = 1}) n).map
            (InvariantsExterior.wedgeQuotient n) := by
  rw [mem_exteriorHodgeClasses_iff,
    ← special_orthogonal_exterior_comparison_aux B hB hs]
  have hi (X : Module.End ℂ (ℂ ⊗[ℚ] V)) (T : Module.End ℂ U)
      (h : e.symm.conj X = T.lTensor (Fin 2 → ℂ)) :=
    exteriorEquiv_intertwines n (splitPowerCoordinates r e) (powerAction r X)
      (m1b_copies (r*2) T) (splitPowerCoordinates_intertwines r e X T h) v
  constructor
  · intro hv T hT
    let X := e.conj (T.lTensor (Fin 2 → ℂ))
    have hX : e.symm.conj X = T.lTensor (Fin 2 → ℂ) := by
      apply LinearMap.ext
      intro z
      simp only [X, LinearEquiv.conj_apply, LinearEquiv.symm_symm,
        LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have hm : X ∈ complexSpan (hodgeLieAlgebra H hH).toSubmodule := by
      apply (hc X).mpr
      refine ⟨T, ⟨hT, hX⟩, ?_⟩
      intro S hS
      have heq : S.lTensor (Fin 2 → ℂ) = T.lTensor (Fin 2 → ℂ) := hS.2.symm.trans hX
      have hh := LinearMap.congr_fun heq ((Pi.single 0 1 : Fin 2 → ℂ) ⊗ₜ[ℂ] (0 : U))
      apply LinearMap.ext
      intro u
      have hh := LinearMap.congr_fun heq ((Pi.single 0 1 : Fin 2 → ℂ) ⊗ₜ[ℂ] u)
      have hh' := congrArg (fun z => splitRowCoordinates z 0) hh
      simpa [splitRowCoordinates, TensorProduct.piScalarRight,
        TensorProduct.piScalarRightHom, TensorProduct.piScalarRightHomBil,
        LinearMap.lTensor_tmul] using hh'
    rw [← hi X T hX, hv X hm]
    exact map_zero (exteriorEquiv n (splitPowerCoordinates r e))
  · intro hv X hX
    obtain ⟨T, ⟨hT, he⟩, _⟩ := (hc X).mp hX
    apply (exteriorEquiv n (splitPowerCoordinates r e)).injective
    rw [hi X T he, hv T hT]
    exact (map_zero (exteriorEquiv n (splitPowerCoordinates r e))).symm

end HodgeLean.Foundations.Abdulali
