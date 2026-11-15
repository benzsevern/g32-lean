import HodgeLean.Foundations.Program.TorusAlgebraizationB52Jets
import HodgeLean.Foundations.Program.TorusAlgebraizationB52LogDerivative

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_directional_eval_factor (z v : b5_V Λ F)
    (u : b5_sections Λ F hF Q 3) (hu : u.val z ≠ 0)
    (hvan : ∀ t : b5_sections Λ F hF Q 3, t.val z = 0 → fderiv ℂ t.val z v = 0) :
    ∃ C : ℂ, ∀ t : b5_sections Λ F hF Q 3, fderiv ℂ t.val z v = C * t.val z := by
  refine ⟨fderiv ℂ u.val z v / u.val z, ?_⟩
  intro t
  let t₀ := t - (t.val z / u.val z) • u
  have ht₀ : t₀.val z = 0 := by
    change t.val z - (t.val z / u.val z) * u.val z = 0
    field_simp
    ring
  have hh := hvan t₀ ht₀
  have hd := congrArg (fun A : b5_V Λ F →L[ℂ] ℂ ↦ A v)
    ((t.property.1 z).hasFDerivAt.sub
      ((u.property.1 z).hasFDerivAt.const_smul (t.val z / u.val z))).fderiv
  have hcalc : fderiv ℂ t₀.val z v = fderiv ℂ t.val z v -
      (t.val z / u.val z) * fderiv ℂ u.val z v := by
    simpa only [t₀, Submodule.coe_sub, Submodule.coe_smul, Pi.sub_def, Pi.smul_def,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] using hd
  rw [hcalc] at hh
  calc
    _ = (t.val z / u.val z) * fderiv ℂ u.val z v := sub_eq_zero.mp hh
    _ = _ := by ring

theorem b52_tangent_of_nonzero_section
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (s : b5_sections Λ F hF Q 1) (hs : s.val ≠ 0)
    (z v : b5_V Λ F) (hv : v ≠ 0) :
    ∃ t : b5_sections Λ F hF Q 3, t.val z = 0 ∧ fderiv ℂ t.val z v ≠ 0 := by
  by_contra hn
  have hvan : ∀ t : b5_sections Λ F hF Q 3, t.val z = 0 → fderiv ℂ t.val z v = 0 := by
    intro t ht
    by_contra hd
    exact hn ⟨t, ht, hd⟩
  obtain ⟨u, hu⟩ := b52_basepoint_of_nonzero_section Λ F hF Q s hs z
  obtain ⟨C, hC⟩ := b52_directional_eval_factor Λ F hF Q z v u hu hvan
  let k := z + z + z
  have hsum : ∀ x, s.val x ≠ 0 → ∀ y, s.val y ≠ 0 → s.val (k - x - y) ≠ 0 →
      fderiv ℂ s.val x v / s.val x + fderiv ℂ s.val y v / s.val y +
        fderiv ℂ s.val (k - x - y) v / s.val (k - x - y) = C := by
    intro x hx y hy hq
    let a := x - z
    let b := y - z
    let c := k - x - y - z
    have habc : a + b + c = 0 := by dsimp [a, b, c, k]; abel
    have hxa : z + a = x := by dsimp [a]; abel
    have hyb : z + b = y := by dsimp [b]; abel
    have hqc : z + c = k - x - y := by dsimp [c]; abel
    let t := b5_balancedCubeSection Λ F hF Q s s s a b c habc
    have htz : t.val z ≠ 0 := by
      change s.val (z + a) * s.val (z + b) * s.val (z + c) ≠ 0
      rw [hxa, hyb, hqc]
      exact mul_ne_zero (mul_ne_zero hx hy) hq
    have hlog := b52_logderiv_translated_triple s.val s.property.1 a b c z v
      (by rwa [hxa]) (by rwa [hyb]) (by rwa [hqc])
    change fderiv ℂ t.val z v / t.val z = _ at hlog
    rw [hC t, mul_div_cancel_right₀ C htz] at hlog
    simpa only [hxa, hyb, hqc] using hlog.symm
  obtain ⟨a, b, c, habc, ha, hb, hc⟩ := b52_balanced_nonzero s.property.1 hs z
  have heq : k - (z + c) - (z + b) = z + a := by
    calc
      _ = z - (a + b + c) + a := by dsimp [k]; abel
      _ = _ := by rw [habc]; simp
  obtain ⟨L, d, hD⟩ := b52_affine_of_balanced_quotient s.val
    (fun x ↦ fderiv ℂ s.val x v) s.property.1
    (b52_differentiable_directional_derivative s.property.1 v) k C hsum
    (z + b) (z + c) hb hc (by rwa [heq])
  exact b52_no_affine_logarithmic_derivative Λ F hF Q hpos s hs v hv L.toLinearMap d hD

end HodgeLean.Foundations.Program
