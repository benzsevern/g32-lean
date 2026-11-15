import HodgeLean.Foundations.Program.MilneTensorScalarNumerator
import HodgeLean.Foundations.Program.MilneTensorTotalOrbit

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_scalar_numerator_on_all_forms {d r n : ℕ}
    (B : LinearMap.BilinForm ℂ (ℂ × (Fin d → ℂ)))
    (hB : B.Nondegenerate) (hsB : ∀ x y, B x y = B y x)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ℂ × (Fin d → ℂ)) ℂ)
    (k : ℕ) (q : MvPolynomial (((Unit ⊕ Fin d) × (Unit ⊕ Fin d)) ⊕
      (Fin n × (Fin r × (Unit ⊕ Fin d)))) ℂ)
    (hq : ∀ (Q : Set.range (m1b_formTransport B)) (a : ℂˣ),
      Q.val.Nondegenerate → (∀ x y, Q.val x y = Q.val y x) → Q.val (1, 0) (1, 0) = a.val →
      ∀ v, MvPolynomial.eval (m1b_scalarFormPoint Q.val v) q =
        a.val ^ k * m1b_orbitExtension B f Q v) :
    ∀ (Q : LinearMap.BilinForm ℂ (ℂ × (Fin d → ℂ))), Q.Nondegenerate →
      (∀ x y, Q x y = Q y x) → Q (1, 0) (1, 0) ≠ 0 → ∀ v,
        MvPolynomial.eval (m1b_scalarFormPoint Q v) q =
          Q (1, 0) (1, 0) ^ k * m1b_totalOrbitExtension B f Q v := by
  intro Q hQ hsQ ha v
  have hmem := m1b_symmetric_forms_same_orbit B Q hB hQ hsB hsQ
  rw [m1b_totalOrbitExtension_on_orbit B f ⟨Q, hmem⟩]
  exact hq ⟨Q, hmem⟩ (Units.mk0 (Q (1, 0) (1, 0)) ha) hQ hsQ rfl v

end HodgeLean.Foundations.Program
