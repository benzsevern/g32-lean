import HodgeLean.Foundations.Program.MilneTensorPairedIntrinsic

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_alternating_pair_orbit_numerator {d r n : ℕ}
    (B : LinearMap.BilinForm ℂ (Fin d → ℂ)) (hB : B.Nondegenerate)
    (haB : ∀ x, B x x = 0)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → (Fin 2 → ℂ) × (Fin d → ℂ)) ℂ)
    (hf : ∀ u ∈ m1b_isometries (m1b_prodBilin m1b_pairForm B),
      ∀ v, f (fun i => m1b_copies r u (v i)) = f v)
    (hsmall : ∀ m (g : MultilinearMap ℂ (fun _ : Fin m => Fin r → Fin d → ℂ) ℂ),
      (∀ u ∈ m1b_isometries B, ∀ v, g (fun i => m1b_copies r u (v i)) = g v) →
      ∃ P : MvPolynomial ((Fin d × Fin d) ⊕ (Fin m × (Fin r × Fin d))) ℂ,
        ∀ (e : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) (v : Fin m → Fin r → Fin d → ℂ),
          MvPolynomial.eval (Sum.elim
            (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
            (fun ij => v ij.1 ij.2.1 ij.2.2)) P = g (fun i j => e.symm (v i j))) :
    ∃ k : ℕ, ∃ q : MvPolynomial (((Fin 2 ⊕ Fin d) × (Fin 2 ⊕ Fin d)) ⊕
        (Fin n × (Fin r × (Fin 2 ⊕ Fin d)))) ℂ,
      ∀ (Q : Set.range (m1b_formTransport (m1b_prodBilin m1b_pairForm B))) (a : ℂˣ),
        Q.val.Nondegenerate → (∀ x, Q.val x x = 0) →
        Q.val (Pi.single 0 1, 0) (Pi.single 1 1, 0) = a.val →
        ∀ v : Fin n → Fin r → (Fin 2 → ℂ) × (Fin d → ℂ),
          MvPolynomial.eval (m1b_pairFormPoint Q.val v) q =
            a.val ^ k * m1b_orbitExtension (m1b_prodBilin m1b_pairForm B) f Q v := by
  obtain ⟨P, hP⟩ := m1b_alternating_pair_local_polynomial B hB haB f hf hsmall
  obtain ⟨k, q, hq⟩ := m1b_pair_intrinsic_numerator P
  refine ⟨k, q, ?_⟩
  intro Q a hQ haQ hp v
  rw [← hq Q.val a hp v, hP Q a hQ haQ hp v]

end HodgeLean.Foundations.Program
