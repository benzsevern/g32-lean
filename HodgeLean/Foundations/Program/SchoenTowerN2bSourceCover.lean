import HodgeLean.Foundations.Program.SchoenTowerN2bPullbackCharts

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- The finite standard chart cover pulled back along the actual source morphism.
Source: Hartshorne, Algebraic Geometry, II.2.5. -/
def n2b_pullbackChartCover {X : Scheme.{0}} {n : ℕ} (ψ : X ⟶ g3c_P n) :
    X.OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (n + 1)) (n2b_pullbackChart ψ)
    (n2b_pullbackChartι ψ) (by
      intro x
      obtain ⟨i, hi⟩ := g3c_chartι_covers n (ψ x)
      refine ⟨i, ?_⟩
      change x ∈ (pullback.fst ψ (g3c_chartι n i)).opensRange
      rw [Scheme.Hom.opensRange_pullbackFst]
      exact hi)

/-- The actual source cover indexed by its nonempty standard charts.
Source: Hartshorne, Algebraic Geometry, II.2.5. -/
def n2b_nonemptyPullbackChartCover {X : Scheme.{0}} {n : ℕ} (ψ : X ⟶ g3c_P n) :
    X.OpenCover :=
  Scheme.Cover.mkOfCovers {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)}
    (fun i => n2b_pullbackChart ψ i.val) (fun i => n2b_pullbackChartι ψ i.val) (by
      intro x
      let 𝒰 := n2b_pullbackChartCover ψ
      obtain ⟨y, hy⟩ := 𝒰.covers x
      exact ⟨⟨𝒰.idx x, ⟨y⟩⟩, y, hy⟩)

end HodgeLean.Foundations.Program
