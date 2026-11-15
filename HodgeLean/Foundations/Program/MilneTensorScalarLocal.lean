import HodgeLean.Foundations.Program.MilneTensorScalarSchur

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_symmetric_scalar_local_polynomial {d r n : ℕ}
    (B : LinearMap.BilinForm ℂ (Fin d → ℂ)) (hB : B.Nondegenerate)
    (hsB : ∀ x y, B x y = B y x)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ℂ × (Fin d → ℂ)) ℂ)
    (hf : ∀ u ∈ m1b_isometries (m1b_prodBilin (LinearMap.mul ℂ ℂ) B),
      ∀ v, f (fun i => m1b_copies r u (v i)) = f v)
    (hsmall : ∀ m (g : MultilinearMap ℂ (fun _ : Fin m => Fin r → Fin d → ℂ) ℂ),
      (∀ u ∈ m1b_isometries B, ∀ v, g (fun i => m1b_copies r u (v i)) = g v) →
      ∃ P : MvPolynomial ((Fin d × Fin d) ⊕ (Fin m × (Fin r × Fin d))) ℂ,
        ∀ (e : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) (v : Fin m → Fin r → Fin d → ℂ),
          MvPolynomial.eval (Sum.elim
            (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
            (fun ij => v ij.1 ij.2.1 ij.2.2)) P = g (fun i j => e.symm (v i j))) :
    ∃ P : MvPolynomial ((Unit ⊕ (Fin d × Fin d)) ⊕
        (Fin n × (Fin r ⊕ (Fin r × Fin d)))) ℂ,
      ∀ (Q : Set.range (m1b_formTransport (m1b_prodBilin (LinearMap.mul ℂ ℂ) B)))
        (a : ℂˣ), Q.val.Nondegenerate → (∀ x y, Q.val x y = Q.val y x) →
        Q.val (1, 0) (1, 0) = a.val →
        ∀ v : Fin n → Fin r → ℂ × (Fin d → ℂ),
          MvPolynomial.eval (Sum.elim
            (Sum.elim (fun _ => a.val)
              (fun ij => m1b_scalarSchur Q.val a (Pi.single ij.1 1) (Pi.single ij.2 1)))
            (fun jc => Sum.elim
              (fun c => (v jc.1 c).1 + a.inv * m1b_scalarCross Q.val (v jc.1 c).2)
              (fun ci => (v jc.1 ci.1).2 ci.2) jc.2)) P =
            m1b_orbitExtension (m1b_prodBilin (LinearMap.mul ℂ ℂ) B) f Q v := by
  obtain ⟨P, hP⟩ := m1b_scalar_split_polynomial (LinearMap.mul ℂ ℂ) B f hf hsmall
  refine ⟨P, ?_⟩
  intro Q a hQ hsQ ha v
  obtain ⟨t, e, ht, he, hreal⟩ := m1b_symmetric_scalar_chart_exists B hB hsB Q.val hQ hsQ a ha
  rw [m1b_orbitExtension_eval _ f hf Q
    (m1b_scalarChartEquiv t (a.inv • m1b_scalarCross Q.val) e).symm hreal]
  have h := hP e t.val
    (fun i c => (v i c).1 + a.inv * m1b_scalarCross Q.val (v i c).2)
    (fun i c => (v i c).2)
  rw [ht, he] at h
  exact h

end HodgeLean.Foundations.Program
