import HodgeLean.Foundations.Program.SchoenTowerN2bGeometricDenominators
import HodgeLean.Foundations.Program.SchoenTowerN2bPullbackCharts

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- Actual source sections have a common positive regularizing power of normalized projective coordinates. -/
theorem n2b_uniform_pullbackChart_representatives
    {X : Scheme.{0}} [IsIntegral X] {n : ℕ}
    (ψ : X ⟶ g3c_P n) [IsAffineHom ψ]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (idx : ι → Fin (n + 1)) [∀ a, Nonempty (n2b_pullbackChart ψ (idx a))]
    (c : κ → ι) (v : ∀ k, Γ(n2b_pullbackChart ψ (idx (c k)), ⊤)) :
    ∃ N : ℕ, 0 < N ∧ ∀ k b,
      ∃ a : Γ(n2b_pullbackChart ψ (idx b), ⊤),
        n2b_openChartRationalMap (n2b_pullbackChartι ψ (idx (c k))) (v k) *
            n2b_openChartRationalMap (n2b_pullbackChartι ψ (idx b))
              (n2b_pullbackChartCoord ψ (idx b) (idx (c k))) ^ N =
          n2b_openChartRationalMap (n2b_pullbackChartι ψ (idx b)) a := by
  apply n2b_uniform_chart_rational_representatives
    (fun a => n2b_pullbackChart ψ (idx a))
    (fun a => n2b_pullbackChartι ψ (idx a))
    (fun a b => n2b_pullbackChartCoord ψ (idx b) (idx a)) ?_ c v
  intro a b
  rw [Scheme.Hom.opensRange_pullbackSnd]
  exact n2b_pullbackChart_preimage_chart ψ (idx b) (idx a)

end HodgeLean.Foundations.Program
