import HodgeLean.Foundations.Program.MilneTensorPairedTransport

noncomputable section
namespace HodgeLean.Foundations.Program
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem m1b_pairScale_pairing (a : ℂˣ) (x y : Fin 2 → ℂ) :
    m1b_pairForm (m1b_pairScaleEquiv a x) (m1b_pairScaleEquiv a y) =
      a.val * m1b_pairForm x y := by
  change (a.val * x 0) * (1 * y 1) - (1 * x 1) * (a.val * y 0) =
    a.val * (x 0 * y 1 - x 1 * y 0)
  ring

theorem m1b_pair_chart_realizes (B : LinearMap.BilinForm ℂ W)
    (Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × W)) (ha : ∀ x, Q x x = 0)
    (a : ℂˣ) (hp : Q (Pi.single 0 1, 0) (Pi.single 1 1, 0) = a.val)
    (e : W ≃ₗ[ℂ] W) (he : m1b_formTransport B e = m1b_pairSchur Q a) :
    m1b_formTransport (m1b_prodBilin m1b_pairForm B)
      (m1b_pairChartEquiv a (m1b_pairShear Q a) e).symm = Q := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change m1b_pairForm (m1b_pairScaleEquiv a (x.1 + m1b_pairShear Q a x.2))
    (m1b_pairScaleEquiv a (y.1 + m1b_pairShear Q a y.2)) +
      B (e.symm x.2) (e.symm y.2) = Q x y
  rw [m1b_pairScale_pairing]
  have hxy := LinearMap.congr_fun (LinearMap.congr_fun he x.2) y.2
  change B (e.symm x.2) (e.symm y.2) = m1b_pairSchur Q a x.2 y.2 at hxy
  rw [hxy]
  exact (m1b_pair_schur_decomposition Q ha a hp x y).symm

theorem m1b_alternating_pair_chart_exists [FiniteDimensional ℂ W]
    (B : LinearMap.BilinForm ℂ W) (hB : B.Nondegenerate) (haB : ∀ x, B x x = 0)
    (Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × W)) (hQ : Q.Nondegenerate)
    (haQ : ∀ x, Q x x = 0) (a : ℂˣ)
    (hp : Q (Pi.single 0 1, 0) (Pi.single 1 1, 0) = a.val) :
    ∃ e : W ≃ₗ[ℂ] W, m1b_formTransport B e = m1b_pairSchur Q a ∧
      m1b_formTransport (m1b_prodBilin m1b_pairForm B)
        (m1b_pairChartEquiv a (m1b_pairShear Q a) e).symm = Q := by
  obtain ⟨e, he⟩ := m1b_alternating_forms_same_orbit B (m1b_pairSchur Q a)
    hB (m1b_pair_schur_nondegenerate Q haQ hQ a hp) haB
    (m1b_pair_schur_alternating Q haQ a)
  exact ⟨e, he, m1b_pair_chart_realizes B Q haQ a hp e he⟩

end HodgeLean.Foundations.Program
