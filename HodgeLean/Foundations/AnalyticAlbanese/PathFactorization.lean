import HodgeLean.Foundations.AnalyticAlbanese.Defs

/-! # Factor evaluation along paths

HC no distance; AV milestone no distance.
-/

noncomputable section
open Manifold
open scoped TensorProduct ContDiff
open HodgeLean.Foundations.Program

namespace HodgeLean.Foundations.AnalyticAlbanese

/-- The representative equation along paths determines evaluation on the Abel map.
HC no distance; AV milestone no distance. -/
theorem factor_evaluation_of_paths
    (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C] [ConnectedSpace C]
    (Μ : Type) [AddCommGroup Μ] (G : Submodule ℂ (ℂ ⊗[ℤ] Μ))
    (p₀ : C) (f : C → b2_torus Μ G) (hbase : f p₀ = 0)
    (aj : C → b3_Jacobian E C) (haj : b3_IsAbelJacobi E C p₀ aj)
    (L : ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) →ₗ[ℂ]
      ((ℂ ⊗[ℤ] Μ) ⧸ G))
    (hL : ∀ l : b3_periodLattice E C,
      L (b2_latticeMap _ (b3_periodF E C) l) ∈ (b2_latticeMap Μ G).range)
    (hpath : ∀ (path : ℝ → C), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 path →
      ∀ v : ℂ ⊗[ℤ] b3_periodLattice E C,
        b3_cplxPeriod E C v = b3_pathPeriod E C path →
        (QuotientAddGroup.mk (L (Submodule.Quotient.mk v)) : b2_torus Μ G) =
          f (path 1) - f (path 0)) :
    ∀ p, descend (b3_periodF E C) G L hL (aj p) = f p := by
  intro p
  obtain ⟨γ, hγ⟩ := b3A_joined (E := E) p₀ p
  obtain ⟨v, hv, hajv⟩ := haj.2 γ hγ.1
  have heq := hpath γ hγ.1 v hv
  rw [hγ.apply_one, hγ.apply_zero, hbase, sub_zero] at heq
  rw [hγ.apply_one, hγ.apply_zero, haj.1, sub_zero] at hajv
  rw [hajv]
  exact heq

end HodgeLean.Foundations.AnalyticAlbanese
