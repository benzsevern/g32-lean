import HodgeLean.Foundations.Abdulali.ExteriorMatrixCoefficient
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- A differentiable one-parameter representation fixes any vector whose orbit
has zero velocity, tested against all algebraic linear functionals. -/
theorem oneParameter_fixed_of_dual_velocity_zero
    {M : Type*} [AddCommGroup M] [Module ℂ M]
    (C : ℂ → Module.End ℂ M) (hzero : C 0 = 1)
    (hadd : ∀ s t, C (s + t) = C s * C t) (v : M)
    (hd : ∀ ℓ : Module.Dual ℂ M, HasDerivAt (fun t => ℓ (C t v)) 0 0)
    (t : ℂ) : C t v = v := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro ℓ
  have hder (s : ℂ) : HasDerivAt (fun t => ℓ (C t v)) 0 s := by
    have hf : (fun t => ℓ (C t v)) =
        fun t => (ℓ.comp (C s)) (C (t - s) v) := by
      funext t
      simp only [LinearMap.comp_apply, ← Module.End.mul_apply, ← hadd, add_sub_cancel]
    rw [hf]
    have h := hd (ℓ.comp (C s))
    have h' : HasDerivAt (fun t => (ℓ.comp (C s)) (C t v)) 0 (s-s) := by
      rw [sub_self]
      exact h
    exact h'.comp_sub_const s s
  have he := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
    (fun s => (hder s).deriv) t 0
  simpa only [map_sub, hzero, Module.End.one_apply, sub_eq_zero] using he

/-- Exterior matrix coefficients differentiate along the exponential curve to
the exterior derivation, in arbitrary finite coordinates. -/
theorem exterior_exp_dual_hasDerivAt_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}
    (b : Module.Basis (Fin d) ℂ V) (r n : ℕ)
    (X : Matrix (Fin d) (Fin d) ℂ) (v : ⋀[ℂ]^n (Fin r → V))
    (ℓ : Module.Dual ℂ (⋀[ℂ]^n (Fin r → V))) :
    HasDerivAt (fun t : ℂ => ℓ (exteriorPower.map n
      (m2_diagonalEnd r (Matrix.toLin b b (NormedSpace.exp (t • X)))) v))
      (ℓ (InvariantsExterior.exteriorDer n
        (m2_diagonalEnd r (Matrix.toLin b b X)) v)) 0 := by
  classical
  let c := (m2_piBasis b r).exteriorPower n
  have hcoord (i : Set.powersetCard (Fin (d*r)) n) :=
    g2k_hasDerivAt_differential (fun t => NormedSpace.exp (t • X)) X 0
      (by simp only [zero_smul, NormedSpace.exp_zero])
      (fun i j => by simpa using g2k_hasDerivAt_exp_mul X 1 0 i j)
      (exteriorMatrixCoefficient b r n v i)
  simp_rw [eval_exteriorMatrixCoefficient, differential_exteriorMatrixCoefficient] at hcoord
  have hexp (z : ⋀[ℂ]^n (Fin r → V)) :
      ℓ z = ∑ i, c.repr z i * ℓ (c i) := by
    conv_lhs => rw [← c.sum_repr z]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, smul_eq_mul])
  convert HasDerivAt.fun_sum (fun i _ => (hcoord i).mul_const (ℓ (c i))) using 1
  · funext t
    exact hexp _
  · exact hexp _

/-- Infinitesimal fixedness integrates along every matrix exponential on
exterior powers of any number of standard copies. -/
theorem exterior_exp_fixed_of_killed
    {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}
    (b : Module.Basis (Fin d) ℂ V) (r n : ℕ)
    (X : Matrix (Fin d) (Fin d) ℂ) (v : ⋀[ℂ]^n (Fin r → V))
    (hv : InvariantsExterior.exteriorDer n
      (m2_diagonalEnd r (Matrix.toLin b b X)) v = 0) (t : ℂ) :
    exteriorPower.map n
      (m2_diagonalEnd r (Matrix.toLin b b (NormedSpace.exp (t • X)))) v = v := by
  let C := fun t : ℂ => exteriorPower.map n
    (m2_diagonalEnd r (Matrix.toLin b b (NormedSpace.exp (t • X))))
  apply oneParameter_fixed_of_dual_velocity_zero C ?_ ?_ v ?_ t
  · change exteriorPower.map n (m2_diagonalEnd r (Matrix.toLin b b
      (NormedSpace.exp ((0 : ℂ) • X)))) = 1
    simp only [zero_smul, NormedSpace.exp_zero, Matrix.toLin_one]
    have hi : m2_diagonalEnd (K := ℂ) (V := V) r LinearMap.id = LinearMap.id := by
      ext w j
      rfl
    rw [hi, exteriorPower.map_id]
    rfl
  · intro s t
    dsimp only [C]
    rw [g2k_exp_add, Matrix.toLin_mul b b b]
    have hm (A D : Module.End ℂ V) : m2_diagonalEnd r (A.comp D) =
        (m2_diagonalEnd r A).comp (m2_diagonalEnd r D) := by ext w j; rfl
    rw [hm, exteriorPower.map_comp]
    rfl
  · intro ℓ
    simpa only [hv, map_zero] using exterior_exp_dual_hasDerivAt_zero b r n X v ℓ

end HodgeLean.Foundations.Abdulali
