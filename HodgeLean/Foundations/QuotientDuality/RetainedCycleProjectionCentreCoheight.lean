import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionCentre
import HodgeLean.Adapters.IntersectionProductScaf
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension

/-! # Coheight of the actual projection centre -/

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The ambient cone dimension bound gives the required coheight at every point of the actual centre. -/
lemma retained_projection_centre_coheight {N n : ℕ}
    (ℓ : Matrix (Fin (n+1)) (Fin (N+1)) ℂ)
    (hb : ∀ Q : Ideal (MvPolynomial (Fin (N+1)) ℂ), Q.IsPrime →
      (∃ j, MvPolynomial.X j ∉ Q) → (∀ i, a3r_lin ℓ (MvPolynomial.X i) ∈ Q) →
      ringKrullDim (MvPolynomial (Fin (N+1)) ℂ ⧸ Q) + (n+1 : ℕ) ≤
        ringKrullDim (MvPolynomial (Fin (N+1)) ℂ))
    (x : a3m_Pn N) (hx : ∀ i, a3r_lin ℓ (MvPolynomial.X i) ∈ (a3m_projCharts N).prime x) :
    ((n+1 : ℕ) : ℕ∞) ≤ Order.coheight x := by
  letI : IsIntegral (a3h_PnO N).left := IntersectionProductScaf_projective_integral N
  let C := a3m_projCharts N
  let _ : ∀ j, Algebra ℂ (C.T j) := fun j => ((C.θ j).comp MvPolynomial.C).toAlgebra
  obtain ⟨-, m, hm, -⟩ := a1d_height_eq_trdeg (X := a3h_PnO N) x
  have hsum := a3m_height_add_coheight (a3h_PnO N) x
  have hdim : TopologicalSpace.dim (a3h_PnO N).left = N := s0_complex_projective_dimension N
  rw [properCycle_height_generic, hdim, hm] at hsum
  have hcfin : Order.coheight x ≠ ⊤ := by
    intro h
    rw [h, add_top] at hsum
    exact ENat.top_ne_natCast N hsum
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hcfin
  rw [← hc] at hsum
  have hmc : m+c = N := by exact_mod_cast hsum
  have hh := a3m_SpecCharts.height_add_one (Y := a3h_PnO N) C (fun _ _ => rfl) x
  have hrel : ∃ j, MvPolynomial.X j ∉ C.prime x :=
    ⟨C.chart x, fun h => (C.X_mem_prime_iff x _).mp h (C.mem_chart x)⟩
  have hd := hb (C.prime x) (C.isPrime_prime x) hrel hx
  have hR : ringKrullDim (MvPolynomial (Fin (N+1)) ℂ) = (N+1 : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      ENat.card_eq_coe_fintype_card]
    simp
  rw [← hh, hm, hR] at hd
  have hmn : m+1+(n+1) ≤ N+1 := by exact_mod_cast hd
  rw [← hc]
  exact_mod_cast (show n+1 ≤ c by omega)

end HodgeLean.Foundations.QuotientDuality
