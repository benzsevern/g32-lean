import HodgeLean.Foundations.Program.MilneTensorPairedRealization

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_alternating_pair_local_polynomial {d r n : ℕ}
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
    ∃ P : MvPolynomial ((Unit ⊕ (Fin d × Fin d)) ⊕
        (Fin n × ((Fin r × Fin 2) ⊕ (Fin r × Fin d)))) ℂ,
      ∀ (Q : Set.range (m1b_formTransport (m1b_prodBilin m1b_pairForm B))) (a : ℂˣ),
        Q.val.Nondegenerate → (∀ x, Q.val x x = 0) →
        Q.val (Pi.single 0 1, 0) (Pi.single 1 1, 0) = a.val →
        ∀ v : Fin n → Fin r → (Fin 2 → ℂ) × (Fin d → ℂ),
          MvPolynomial.eval (Sum.elim
            (Sum.elim (fun _ => a.val)
              (fun ij => m1b_pairSchur Q.val a (Pi.single ij.1 1) (Pi.single ij.2 1)))
            (fun jc => Sum.elim
              (fun ci => ((v jc.1 ci.1).1 + m1b_pairShear Q.val a (v jc.1 ci.1).2) ci.2)
              (fun ci => (v jc.1 ci.1).2 ci.2) jc.2)) P =
            m1b_orbitExtension (m1b_prodBilin m1b_pairForm B) f Q v := by
  obtain ⟨P, hP⟩ := m1b_paired_split_polynomial m1b_pairForm B f hf hsmall
  refine ⟨P, ?_⟩
  intro Q a hQ haQ hp v
  obtain ⟨e, he, hreal⟩ := m1b_alternating_pair_chart_exists B hB haB Q.val hQ haQ a hp
  rw [m1b_orbitExtension_eval _ f hf Q
    (m1b_pairChartEquiv a (m1b_pairShear Q.val a) e).symm hreal]
  have h := hP e a.val
    (fun i c => (v i c).1 + m1b_pairShear Q.val a (v i c).2)
    (fun i c => (v i c).2)
  rw [he] at h
  have hscale (u : Fin 2 → ℂ) : m1b_pairScaleEquiv a u =
      fun k => (if k = 0 then a.val else 1) * u k := by
    funext k
    change (if k = 0 then a else (1 : ℂˣ)).val * u k =
      (if k = 0 then a.val else 1) * u k
    by_cases hk : k = 0 <;> simp [hk]
  change MvPolynomial.eval _ P = f (fun i c =>
    (m1b_pairScaleEquiv a ((v i c).1 + m1b_pairShear Q.val a (v i c).2), e.symm (v i c).2))
  simpa only [hscale] using h

end HodgeLean.Foundations.Program
