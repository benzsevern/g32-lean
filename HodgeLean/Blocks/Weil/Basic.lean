import HodgeLean.Blocks.HodgeStructure.Morphisms

/-! # Weil-type weight-one Hodge structures -/

open scoped TensorProduct ComplexConjugate

noncomputable section

namespace HodgeBlocks

/-- A chosen quadratic presentation of an imaginary quadratic field.

Every imaginary quadratic field admits a presentation `ℚ(√-d)` with `d > 0`, so an arbitrary
instance of this bundle represents an arbitrary imaginary quadratic field, rather than selecting
or narrowing to one particular field. -/
structure ImaginaryQuadraticData (K : Type*) [Field K] [Algebra ℚ K] where
  omega : K
  d : ℚ
  d_pos : 0 < d
  omega_sq : omega ^ 2 = algebraMap ℚ K (-d)
  span : ∀ x : K, ∃ a b : ℚ, x = algebraMap ℚ K a + b • omega

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- The economical datum needed from a `K`-action: the image `J` of the chosen square root,
its quadratic relation, and preservation of every Hodge piece.  A full `Module K V` is not
constructed because none of the eigenspace arguments requires one. -/
structure WeilAction (M : QHodgeStructure 1 V) (d : ℚ) where
  J : V →ₗ[ℚ] V
  J_sq : J.comp J = (-d) • LinearMap.id
  preserves : ∀ pq : ℤ × ℤ, (M.H pq).map (J.baseChange ℂ) ≤ M.H pq

namespace WeilAction

variable {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d)

/-- The complexification of the rational endomorphism `J`. -/
abbrev Jc : Module.End ℂ (ℂ ⊗[ℚ] V) := A.J.baseChange ℂ

/-- The distinguished square root `i√d` in `ℂ`. -/
def omegaC (d : ℚ) : ℂ := Complex.I * (Real.sqrt (d : ℝ) : ℂ)

/-- The `i√d` eigenspace of `J`. -/
def Vs : Submodule ℂ (ℂ ⊗[ℚ] V) := Module.End.eigenspace A.Jc (omegaC d)

/-- The `-i√d` eigenspace of `J`. -/
def Vsbar : Submodule ℂ (ℂ ⊗[ℚ] V) := Module.End.eigenspace A.Jc (-omegaC d)

theorem omegaC_sq (hd : 0 < d) : omegaC d ^ 2 = -(d : ℂ) := by
  have hs : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast hd.le)
  rw [omegaC, mul_pow, Complex.I_sq]
  rw [show (Real.sqrt (d : ℝ) : ℂ) ^ 2 = (d : ℂ) by exact_mod_cast hs]
  ring

theorem omegaC_ne_zero (hd : 0 < d) : omegaC d ≠ 0 := by
  intro h
  have := omegaC_sq hd
  rw [h, zero_pow (by norm_num : 2 ≠ 0)] at this
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  exact hd0 (neg_eq_zero.mp this.symm)

/-- Scalar extension respects the quadratic relation for `J`. -/
theorem Jc_sq : A.Jc.comp A.Jc = (-(d : ℂ)) • LinearMap.id := by
  rw [← LinearMap.baseChange_comp, A.J_sq, LinearMap.baseChange_smul,
    LinearMap.baseChange_id]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  change ((-d : ℚ) • x) = (-(d : ℂ)) • x
  rw [neg_smul, neg_smul]
  congr 1

/-- Rational conjugation commutes with the complexification of a rational linear map. -/
theorem sigmaQ_Jc (x : ℂ ⊗[ℚ] V) : sigmaQ V (A.Jc x) = A.Jc (sigmaQ V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
      change sigmaQR V (c ⊗ₜ[ℚ] A.J v) =
        A.Jc (sigmaQR V (c ⊗ₜ[ℚ] v))
      rw [sigmaQ_tmul, sigmaQ_tmul, LinearMap.baseChange_tmul]
  | add x y hx hy => simp [hx, hy]

theorem conj_omegaC : (starRingEnd ℂ) (omegaC d) = -omegaC d := by
  simp [omegaC]

/-- Conjugation exchanges the two Weil eigenspaces. -/
theorem map_Vs_sigmaQ : A.Vs.map (sigmaQ V) = A.Vsbar := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    change x ∈ Module.End.eigenspace A.Jc (omegaC d) at hx
    change sigmaQ V x ∈ Module.End.eigenspace A.Jc (-omegaC d)
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← A.sigmaQ_Jc, hx, map_smulₛₗ, conj_omegaC]
  · intro y hy
    change y ∈ Module.End.eigenspace A.Jc (-omegaC d) at hy
    rw [Module.End.mem_eigenspace_iff] at hy
    refine ⟨sigmaQ V y, ?_, sigmaQ_involutive V y⟩
    change sigmaQ V y ∈ Module.End.eigenspace A.Jc (omegaC d)
    rw [Module.End.mem_eigenspace_iff, ← A.sigmaQ_Jc, hy, map_smulₛₗ]
    simp only [map_neg, conj_omegaC, neg_neg]

/-- The two distinct Weil eigenspaces intersect trivially. -/
theorem inf_Vs_Vsbar (hd : 0 < d) : A.Vs ⊓ A.Vsbar = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hp := (Module.End.mem_eigenspace_iff.mp hx.1)
    have hm := (Module.End.mem_eigenspace_iff.mp hx.2)
    rw [Submodule.mem_bot]
    have hz : ((2 : ℂ) * omegaC d) • x = 0 := by
      calc
        ((2 : ℂ) * omegaC d) • x = omegaC d • x - (-omegaC d) • x := by module
        _ = A.Jc x - A.Jc x := by rw [← hp, ← hm]
        _ = 0 := sub_self _
    exact (smul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) (omegaC_ne_zero hd))
  · exact bot_le

/-- The balanced-dimension condition defining Weil type.  It deliberately avoids natural-number
division, so evenness is part of the assertion rather than hidden by truncation. -/
def IsWeilType : Prop :=
  2 * Module.finrank ℂ ↥(WeilAction.Vs A ⊓ M.H ((1 : ℤ), (0 : ℤ))) =
    Module.finrank ℂ ↥(WeilAction.Vs A)

end WeilAction
end HodgeBlocks
