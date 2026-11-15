import HodgeLean.Foundations.Program.MilneFactorsDefs
import HodgeLean.Foundations.Program.MilneFactorsAdjoint
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import HodgeLean.Foundations.Program.MilneFactorsMatrix
import HodgeLean.Foundations.Program.MilneFactorsBlocks
import HodgeLean.Foundations.Program.MilneFactorsHodgeSemisimple

noncomputable section

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

theorem m1_centralizer_semisimple_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] :
    IsSemisimpleRing (m0_endCentralizer J) := by
  obtain ⟨pol, hP⟩ := m1_exists_positive_polarization J
  exact m1_centralizer_semisimple_of_polarization J hP


theorem m1_centralizer_matrix_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] :
    ∃ (s : ℕ) (d : Fin s → ℕ), (∀ i, 0 < d i) ∧
      Nonempty ((m0_endCentralizer J) ≃ₐ[ℂ]
        ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ)) := by
  letI := (torusCohomology_cupProductOf J).finite
  letI := m1_centralizer_semisimple_aux J
  obtain ⟨s, d, hd, he⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (m0_endCentralizer J)
  exact ⟨s, d, fun i => Nat.pos_of_ne_zero (hd i).out, he⟩

theorem m1_centralizer_involution_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) :
    ∃ τ : (m0_endCentralizer J) ≃ₗ[ℂ] (m0_endCentralizer J),
      Function.Involutive τ ∧
      (∀ a b, τ (a * b) = τ b * τ a) ∧
      (∀ (a : m0_endCentralizer J) (x y : ℂ ⊗[ℚ] HQ J 1),
        m0_form J pol hη ((a : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) x) y =
          m0_form J pol hη x ((τ a : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) y)) := by
  letI := (torusCohomology_cupProductOf J).finite
  let hω := pol1_complexify_nondegenerate hη
  have hp (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) (x y) :
      m0_form J pol hη (u x) y = m0_form J pol hη x (m0_adjoint hω u y) := by
    simpa only [m0_form, polarizationForm, pol1_dualForm_complexify] using
      m0_adjoint_pair hω u x y
  have hm (u : m0_endCentralizer J) : m0_adjoint hω u.val ∈ m0_endCentralizer J := by
    obtain ⟨v, hv, hu⟩ := m0_centralizer_adjoint_aux J pol hη hpos u.val u.property
    have he : m0_adjoint hω u.val = v := by
      apply m1_adjoint_eq_of
      simpa only [m0_form, polarizationForm, pol1_dualForm_complexify] using hv.2
    exact he.symm ▸ hv.1
  let f : m0_endCentralizer J →ₗ[ℂ] m0_endCentralizer J :=
    ((m1_adjointLinear hω).comp (m0_endCentralizer J).val.toLinearMap).codRestrict
      (m0_endCentralizer J).toSubmodule hm
  have hf : Function.Involutive f := by
    intro u
    apply Subtype.ext
    exact m1_adjoint_involutive hω u.val
  let e : m0_endCentralizer J ≃ₗ[ℂ] m0_endCentralizer J :=
    { f with
      invFun := f
      left_inv := hf
      right_inv := hf }
  refine ⟨e, hf, ?_, ?_⟩
  · intro a b
    apply Subtype.ext
    exact m1_adjoint_mul hω a.val b.val
  · intro a x y
    exact hp a.val x y

theorem m1_involution_blocks_aux (s : ℕ) (d : Fin s → ℕ) (hd : ∀ i, 0 < d i)
    (τ : ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃ₗ[ℂ]
      ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ))
    (hτ : Function.Involutive τ) (hmul : ∀ a b, τ (a * b) = τ b * τ a) :
    ∃ σ : Equiv.Perm (Fin s), Function.Involutive σ ∧
      (∀ i, d (σ i) = d i) ∧
      (∀ i, τ (m1_blockId s d i) = m1_blockId s d (σ i)) := by
  obtain ⟨σ, hσ, he⟩ := m1_block_permutation d hd τ hτ hmul
  refine ⟨σ, hσ, ?_, he⟩
  intro i
  exact (m1_block_sizes_equal d τ hτ hmul i (σ i) (he i)).symm


theorem m1_simple_involution_aux (n : ℕ) (hn : 0 < n)
    (τ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hτ : Function.Involutive τ) (hmul : ∀ A B, τ (A * B) = τ B * τ A) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B ∧
      (B.transpose = B ∨ B.transpose = -B) ∧
      ∀ X, τ X = m1_gramAdjoint n B X := by
  let z : Fin n := ⟨0, hn⟩
  obtain ⟨B, hu, hB⟩ := m1_reversal_gram_intertwiner τ hmul z
  refine ⟨B, hu, m1_gram_symmetric_or_alternating τ hτ B hu hB z, ?_⟩
  intro X
  have hd := (Matrix.isUnit_iff_isUnit_det B).mp hu
  calc
    τ X = B⁻¹ * (B * τ X) := (Matrix.nonsing_inv_mul_cancel_left B _ hd).symm
    _ = B⁻¹ * (X.transpose * B) := by rw [hB]
    _ = m1_gramAdjoint n B X := (mul_assoc _ _ _).symm


theorem m1_gram_norm_one_aux (n : ℕ) (B X : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B) :
    m1_gramAdjoint n B X * X = 1 ↔
      IsUnit X ∧ X.transpose * B * X = B := by
  have hdet : IsUnit B.det := hB.map Matrix.detMonoidHom
  constructor
  · intro h
    have hX : IsUnit X := by
      exact isUnit_of_mul_isUnit_right (h.symm ▸ isUnit_one)
    refine ⟨hX, ?_⟩
    have hh := congrArg (fun Y => B * Y) h
    simpa only [m1_gramAdjoint, ← mul_assoc, Matrix.mul_nonsing_inv B hdet,
      one_mul, mul_one] using hh
  · rintro ⟨_, h⟩
    calc
      B⁻¹ * X.transpose * B * X = B⁻¹ * (X.transpose * B * X) := by simp only [mul_assoc]
      _ = 1 := by rw [h, Matrix.nonsing_inv_mul B hdet]

theorem m1_exchange_norm_one_aux (n : ℕ)
    (X : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :
    m1_exchange n X * X = 1 ↔
      ∃ U : (Matrix (Fin n) (Fin n) ℂ)ˣ,
        X = (U.val, U.inv.transpose) := by
  constructor
  · intro h
    have h₁ : X.2.transpose * X.1 = 1 := congrArg Prod.fst h
    have h₂ : X.1 * X.2.transpose = 1 := mul_eq_one_comm.mp h₁
    exact ⟨⟨X.1, X.2.transpose, h₂, h₁⟩, by simp⟩
  · rintro ⟨U, rfl⟩
    apply Prod.ext
    · exact U.inv_val
    · change U.val.transpose * U.inv.transpose = 1
      rw [← Matrix.transpose_mul, U.inv_val, Matrix.transpose_one]

end HodgeLean.Foundations.Program
