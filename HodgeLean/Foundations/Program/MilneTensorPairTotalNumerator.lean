import HodgeLean.Foundations.Program.MilneTensorPairedOrbitNumerator
import HodgeLean.Foundations.Program.MilneTensorTotalOrbit

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_pair_numerator_on_all_forms {d r n : ℕ}
    (B : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × (Fin d → ℂ)))
    (hB : B.Nondegenerate) (haB : ∀ x, B x x = 0)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → (Fin 2 → ℂ) × (Fin d → ℂ)) ℂ)
    (k : ℕ) (q : MvPolynomial (((Fin 2 ⊕ Fin d) × (Fin 2 ⊕ Fin d)) ⊕
      (Fin n × (Fin r × (Fin 2 ⊕ Fin d)))) ℂ)
    (hq : ∀ (Q : Set.range (m1b_formTransport B)) (a : ℂˣ),
      Q.val.Nondegenerate → (∀ x, Q.val x x = 0) →
      Q.val (Pi.single 0 1, 0) (Pi.single 1 1, 0) = a.val →
      ∀ v, MvPolynomial.eval (m1b_pairFormPoint Q.val v) q =
        a.val ^ k * m1b_orbitExtension B f Q v) :
    ∀ Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × (Fin d → ℂ)), Q.Nondegenerate →
      (∀ x, Q x x = 0) → Q (Pi.single 0 1, 0) (Pi.single 1 1, 0) ≠ 0 → ∀ v,
        MvPolynomial.eval (m1b_pairFormPoint Q v) q =
          Q (Pi.single 0 1, 0) (Pi.single 1 1, 0) ^ k * m1b_totalOrbitExtension B f Q v := by
  intro Q hQ haQ hp v
  have hmem := m1b_alternating_forms_same_orbit B Q hB hQ haB haQ
  rw [m1b_totalOrbitExtension_on_orbit B f ⟨Q, hmem⟩]
  exact hq ⟨Q, hmem⟩ (Units.mk0 (Q (Pi.single 0 1, 0) (Pi.single 1 1, 0)) hp) hQ haQ rfl v

end HodgeLean.Foundations.Program
