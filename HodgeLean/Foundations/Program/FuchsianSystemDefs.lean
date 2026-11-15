module

public import HodgeLean.Foundations.Program.HolomorphicODEDefs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-! # Fuchsian coefficients and polygonal transport data -/

public section
noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- The coefficient of a system with finitely many simple poles.
Source: Ilyashenko–Yakovenko, Lectures on Analytic Differential Equations, §16. -/
def b65f_coefficient (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset ℂ) (R : ℂ → E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  ∑ a ∈ s, (z - a)⁻¹ • R a

example : b65f_coefficient ℂ {0} (fun _ ↦ 1) 1 = 1 := by
  simp [b65f_coefficient]

/-- The m-th successive integral along the oriented straight segment from u to v.
Source: Hille, Ordinary Differential Equations in the Complex Domain, §2.3, successive approximations. -/
def b65f_iterated (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) (u v : ℂ) : ℕ → ℝ → E →L[ℂ] E
  | 0, _ => 1
  | m + 1, t => ∫ q in (0 : ℝ)..t,
      (v - u) • (A (u + (q : ℂ) * (v - u)) * b65f_iterated E A u v m q)

example (A : ℂ → ℂ →L[ℂ] ℂ) (u v : ℂ) :
    b65f_iterated ℂ A u v 0 1 = 1 := rfl

/-- The Dyson series along one oriented segment; total even outside its convergence domain.
Source: Hille, Ordinary Differential Equations in the Complex Domain, §2.3. -/
def b65f_segment (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) (u v : ℂ) : E →L[ℂ] E :=
  ∑' m : ℕ, b65f_iterated E A u v m 1

example (A : ℂ → ℂ →L[ℂ] ℂ) (u v : ℂ) :
    b65f_segment ℂ A u v = ∑' m : ℕ, b65f_iterated ℂ A u v m 1 := rfl

/-- Transport on the dyadic polygon through samples of a curve, later factors on the left.
Source: Hille, Ordinary Differential Equations in the Complex Domain, analytic continuation of linear systems. -/
def b65f_polygon (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) (γ : ℝ → ℂ) (N : ℕ) : E →L[ℂ] E :=
  (List.ofFn (fun i : Fin (2 ^ N) ↦ b65f_segment E A
    (γ ((i.val : ℝ) / (2 : ℝ) ^ N))
    (γ (((i.val : ℝ) + 1) / (2 : ℝ) ^ N)))).reverse.prod

example (A : ℂ → ℂ →L[ℂ] ℂ) (γ : ℝ → ℂ) :
    b65f_polygon ℂ A γ 0 = b65f_segment ℂ A (γ 0) (γ 1) := by
  simp [b65f_polygon, List.ofFn_succ]

/-- Limit of dyadic polygon transports, with the topological default outside convergence.
Source: analytic continuation by regular discs and polygonal approximation. -/
def b65f_transport (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) (γ : ℝ → ℂ) : E →L[ℂ] E :=
  limUnder atTop (b65f_polygon E A γ)

example (A : ℂ → ℂ →L[ℂ] ℂ) (γ : ℝ → ℂ) :
    b65f_transport ℂ A γ = limUnder atTop (b65f_polygon ℂ A γ) := rfl

/-- Positive circular loop, based at a + r, with its real parameter extended periodically.
Source: the parametrization z = a + r exp(2πit). -/
def b65f_circle (a : ℂ) (r : ℝ) (t : ℝ) : ℂ :=
  a + (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))

example (a : ℂ) (r : ℝ) : b65f_circle a r 0 = a + r := by
  simp [b65f_circle]

example : 0 < Module.finrank ℂ ℂ := by simp
example : (1 : ℂ →L[ℂ] ℂ) ≠ 0 := by
  intro h
  have := congrArg (fun f : ℂ →L[ℂ] ℂ ↦ f 1) h
  simp at this

example : ∀ k : ℕ, 0 < k → Function.Bijective
    (fun T : ℂ →L[ℂ] ℂ ↦ (k : ℂ) • T -
      (((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) * T -
        T * ((1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)))) := by
  intro k hk
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simpa only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, sub_self, sub_zero]
    using (isUnit_iff_ne_zero.mpr hk').smul_bijective (β := ℂ →L[ℂ] ℂ)

example : AnalyticOnNhd ℂ (fun z : ℂ ↦ z • (1 : ℂ →L[ℂ] ℂ)) univ := by
  intro z hz
  exact analyticAt_id.smul analyticAt_const

example : (fun z : ℂ ↦ z • (1 : ℂ →L[ℂ] ℂ)) 1 ≠
    (fun z : ℂ ↦ z • (1 : ℂ →L[ℂ] ℂ)) 0 := by
  simp

example : Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℂ)) ≠ 1 := by
  have h : 2 * (Real.pi : ℂ) * Complex.I * (1 / 2 : ℂ) = Real.pi * Complex.I := by ring
  rw [h, Complex.exp_pi_mul_I]
  norm_num

end HodgeLean.Foundations.Program
