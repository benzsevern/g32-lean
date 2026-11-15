import HodgeLean.Foundations.Program.MilneTensorScalarHomothety
import HodgeLean.Foundations.Program.MilneTensorPolynomial

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r n : ℕ}

theorem m1b_orbit_polynomial_scalar
    (B : LinearMap.BilinForm ℂ (ι → ℂ))
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (P : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ)
    (hP : ∀ (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin r → ι → ℂ),
      MvPolynomial.eval (Sum.elim
        (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
        (fun tc => v tc.1 tc.2.1 tc.2.2)) P = f (fun t c => e.symm (v t c)))
    (e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (v : Fin n → Fin r → ι → ℂ)
    (c : ℂ) (hc : c ≠ 0) :
    MvPolynomial.eval (Sum.elim
      (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1) * c ^ 2)
      (fun tc => v tc.1 tc.2.1 tc.2.2)) P = c ^ n * f (fun t a => e.symm (v t a)) := by
  let a : ℂˣ := Units.mk0 c hc
  have h := hP (e.trans (LinearEquiv.smulOfUnit a⁻¹)) v
  rw [m1b_formTransport_scalar] at h
  have hs : f (fun t i => (e.trans (LinearEquiv.smulOfUnit a⁻¹)).symm (v t i)) =
      c ^ n * f (fun t i => e.symm (v t i)) := by
    change f (fun t i => e.symm (c • v t i)) = _
    simp only [map_smul]
    change f (fun t => c • (fun i => e.symm (v t i))) = _
    rw [f.map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hs] at h
  simpa only [LinearMap.smul_apply, smul_eq_mul, a, Units.val_mk0, mul_comm] using h

end HodgeLean.Foundations.Program
