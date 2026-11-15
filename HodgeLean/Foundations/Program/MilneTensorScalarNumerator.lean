import HodgeLean.Foundations.Program.MilneTensorScalarLocal
import HodgeLean.Foundations.Program.MilneTensorSchurPolynomial

noncomputable section
namespace HodgeLean.Foundations.Program

def m1b_scalarBasisVector (d : ℕ) : (Unit ⊕ Fin d) → ℂ × (Fin d → ℂ) :=
  Sum.elim (fun _ => (1, 0)) (fun i => (0, Pi.single i 1))

def m1b_scalarFormPoint {d r n : ℕ} (Q : LinearMap.BilinForm ℂ (ℂ × (Fin d → ℂ)))
    (v : Fin n → Fin r → ℂ × (Fin d → ℂ)) :
    (((Unit ⊕ Fin d) × (Unit ⊕ Fin d)) ⊕ (Fin n × (Fin r × (Unit ⊕ Fin d)))) → ℂ :=
  Sum.elim (fun ij => Q (m1b_scalarBasisVector d ij.1) (m1b_scalarBasisVector d ij.2))
    (fun jc => Sum.elim (fun _ => (v jc.1 jc.2.1).1) (v jc.1 jc.2.1).2 jc.2.2)

theorem m1b_scalar_intrinsic_numerator {d r n : ℕ}
    (p : MvPolynomial ((Unit ⊕ (Fin d × Fin d)) ⊕
      (Fin n × (Fin r ⊕ (Fin r × Fin d)))) ℂ) :
    ∃ k : ℕ, ∃ q : MvPolynomial (((Unit ⊕ Fin d) × (Unit ⊕ Fin d)) ⊕
        (Fin n × (Fin r × (Unit ⊕ Fin d)))) ℂ,
      ∀ (Q : LinearMap.BilinForm ℂ (ℂ × (Fin d → ℂ))) (a : ℂˣ),
        Q (1, 0) (1, 0) = a.val → ∀ v : Fin n → Fin r → ℂ × (Fin d → ℂ),
          a.val ^ k * MvPolynomial.eval (Sum.elim
            (Sum.elim (fun _ => a.val)
              (fun ij => m1b_scalarSchur Q a (Pi.single ij.1 1) (Pi.single ij.2 1)))
            (fun jc => Sum.elim
              (fun c => (v jc.1 c).1 + a.inv * m1b_scalarCross Q (v jc.1 c).2)
              (fun ci => (v jc.1 ci.1).2 ci.2) jc.2)) p =
            MvPolynomial.eval (m1b_scalarFormPoint Q v) q := by
  obtain ⟨k, q, hq⟩ := m1b_symmetric_chart_numerator
    (τ := ((Unit ⊕ Fin d) × (Unit ⊕ Fin d)) ⊕ (Fin n × (Fin r × (Unit ⊕ Fin d))))
    (MvPolynomial.X (Sum.inl (Sum.inl (), Sum.inl ())))
    (fun i => MvPolynomial.X (Sum.inl (Sum.inl (), Sum.inr i)))
    (fun i j => MvPolynomial.X (Sum.inl (Sum.inr i, Sum.inr j)))
    (fun j c => MvPolynomial.X (Sum.inr (j, c, Sum.inl ())))
    (fun j c i => MvPolynomial.X (Sum.inr (j, c, Sum.inr i))) p
  refine ⟨k, q, ?_⟩
  intro Q a ha v
  have h := hq (m1b_scalarFormPoint Q v) (by
    simpa only [MvPolynomial.eval_X, m1b_scalarFormPoint, m1b_scalarBasisVector,
      Sum.elim_inl, ha] using a.ne_zero)
  simp only [MvPolynomial.eval_X, m1b_scalarFormPoint, m1b_scalarBasisVector,
    Sum.elim_inl, Sum.elim_inr, ha] at h
  convert h using 1
  congr 2
  congr 1
  funext j
  rcases j with ((j | ij) | ⟨j, c | ci⟩)
  · rfl
  · change Q (0, Pi.single ij.1 1) (0, Pi.single ij.2 1) -
      a.inv * (m1b_scalarCross Q (Pi.single ij.1 1) * m1b_scalarCross Q (Pi.single ij.2 1)) =
        Q (0, Pi.single ij.1 1) (0, Pi.single ij.2 1) -
          m1b_scalarCross Q (Pi.single ij.1 1) * m1b_scalarCross Q (Pi.single ij.2 1) / a.val
    rw [Units.inv_eq_val_inv, Units.val_inv_eq_inv_val, div_eq_mul_inv]
    ring
  · change (v j c).1 + a.inv * m1b_scalarCross Q (v j c).2 =
      (v j c).1 + (∑ i, m1b_scalarCross Q (Pi.single i 1) * (v j c).2 i) / a.val
    rw [m1b_dual_apply_coordinates d (m1b_scalarCross Q) (v j c).2,
      Units.inv_eq_val_inv, Units.val_inv_eq_inv_val, div_eq_mul_inv]
    have hsum : (∑ i, (v j c).2 i * m1b_scalarCross Q (Pi.single i 1)) =
        ∑ i, m1b_scalarCross Q (Pi.single i 1) * (v j c).2 i := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    rw [hsum, mul_comm]
  · rfl
  all_goals rfl

theorem m1b_symmetric_scalar_orbit_numerator {d r n : ℕ}
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
    ∃ k : ℕ, ∃ q : MvPolynomial (((Unit ⊕ Fin d) × (Unit ⊕ Fin d)) ⊕
        (Fin n × (Fin r × (Unit ⊕ Fin d)))) ℂ,
      ∀ (Q : Set.range (m1b_formTransport (m1b_prodBilin (LinearMap.mul ℂ ℂ) B)))
        (a : ℂˣ), Q.val.Nondegenerate → (∀ x y, Q.val x y = Q.val y x) →
        Q.val (1, 0) (1, 0) = a.val →
        ∀ v : Fin n → Fin r → ℂ × (Fin d → ℂ),
          MvPolynomial.eval (m1b_scalarFormPoint Q.val v) q =
            a.val ^ k * m1b_orbitExtension (m1b_prodBilin (LinearMap.mul ℂ ℂ) B) f Q v := by
  obtain ⟨P, hP⟩ := m1b_symmetric_scalar_local_polynomial B hB hsB f hf hsmall
  obtain ⟨k, q, hq⟩ := m1b_scalar_intrinsic_numerator P
  refine ⟨k, q, ?_⟩
  intro Q a hQ hsQ ha v
  rw [← hq Q.val a ha v, hP Q a hQ hsQ ha v]

end HodgeLean.Foundations.Program
