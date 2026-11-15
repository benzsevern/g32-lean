import HodgeLean.Foundations.Program.CurveJacobianAPlumbing

/-! # Track B3, lane A: holomorphic forms on the plane

The forms `p(z) dz`, for polynomials `p`, are holomorphic on `ℂ` and independent, so `Ω¹(ℂ)` is
infinite-dimensional.
-/

noncomputable section

open Manifold Filter Topology Polynomial
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section Plane

/-- In the trivializations of the tangent bundle of the plane the fibre coordinate is the vector. -/
theorem b3A_plane_triv_snd (x₀ : ℂ) (p : TangentBundle 𝓘(ℂ, ℂ) ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) x₀ p).2 = p.2 := by
  rw [TangentBundle.trivializationAt_apply]
  simp
  rfl

/-- The form `p(z) dz` of a polynomial `p` on the plane. -/
def b3A_polyForm (p : ℂ[X]) : TangentBundle 𝓘(ℂ, ℂ) ℂ → ℂ := fun q ↦ p.eval q.1 * (show ℂ from q.2)

/-- Polynomial functions are analytic. -/
theorem b3A_poly_contDiff (p : ℂ[X]) : ContDiff ℂ ω (fun z : ℂ ↦ p.eval z) := by
  have : (fun z : ℂ ↦ p.eval z) =
      fun z ↦ ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * z ^ i := by
    funext z
    exact p.eval_eq_sum_range z
  rw [this]
  exact ContDiff.sum fun i _ ↦ contDiff_const.mul (contDiff_id.pow i)

/-- `p(z) dz` is a holomorphic form. -/
theorem b3A_polyForm_mem (p : ℂ[X]) : b3A_polyForm p ∈ b3_HolForm ℂ ℂ := by
  refine ⟨fun q ↦ ?_, fun x a v w ↦ ?_⟩
  · set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) q.1
    have hq : q ∈ e.source := by
      rw [TangentBundle.trivializationAt_source]
      exact mem_chart_source ℂ q.proj
    have h1 := (e.contMDiffOn (n := ω) (IB := 𝓘(ℂ, ℂ)) q hq).contMDiffAt
      (e.open_source.mem_nhds hq)
    have h2 : ContMDiff (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ)) 𝓘(ℂ, ℂ) ω
        (fun r : ℂ × ℂ ↦ p.eval r.1 * r.2) :=
      ((b3A_poly_contDiff p).contMDiff.comp contMDiff_fst).mul contMDiff_snd
    refine ((h2 _).comp q h1).congr_of_eventuallyEq ?_
    filter_upwards [e.open_source.mem_nhds hq] with r hr
    simp only [Function.comp_apply, b3A_polyForm, e, b3A_plane_triv_snd]
    rfl
  · change p.eval x * (a * (show ℂ from v) + (show ℂ from w)) =
      a * (p.eval x * (show ℂ from v)) + p.eval x * (show ℂ from w)
    ring

/-- The forms `p(z) dz`, as a linear map from polynomials. -/
def b3A_polyFormMap : ℂ[X] →ₗ[ℂ] b3_HolForm ℂ ℂ where
  toFun p := ⟨b3A_polyForm p, b3A_polyForm_mem p⟩
  map_add' p q := by
    ext r
    simp only [b3A_polyForm, eval_add, Submodule.coe_add, Pi.add_apply]
    exact add_mul _ _ (show ℂ from r.snd)
  map_smul' c p := by
    ext r
    simp only [b3A_polyForm, eval_smul, smul_eq_mul, Submodule.coe_smul, Pi.smul_apply]
    exact mul_assoc _ _ (show ℂ from r.snd)

/-- Distinct polynomials give distinct forms. -/
theorem b3A_polyFormMap_injective : Function.Injective b3A_polyFormMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  refine Polynomial.funext fun z ↦ ?_
  have := congrArg (fun θ : b3_HolForm ℂ ℂ ↦ (θ : TangentBundle 𝓘(ℂ, ℂ) ℂ → ℂ) ⟨z, (show TangentSpace 𝓘(ℂ, ℂ) z from (1 : ℂ))⟩) hp
  simpa [b3A_polyFormMap, b3A_polyForm] using this

/-- **Holomorphic forms on the plane are infinite-dimensional.** -/
theorem b3A_complexPlane_not_finiteDimensional : ¬ FiniteDimensional ℂ (b3_HolForm ℂ ℂ) := by
  intro h
  have : Module.Finite ℂ ℂ[X] := Module.Finite.of_injective _ b3A_polyFormMap_injective
  have := Module.Finite.finite_basis (Polynomial.basisMonomials ℂ)
  exact not_finite ℕ

end Plane

end HodgeLean.Foundations.Program
