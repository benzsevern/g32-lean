import HodgeLean.Foundations.Analytic.ComplexAnalyticSpace
import HodgeLean.Foundations.ChowTheorem

noncomputable section
open scoped Manifold ContDiff
open HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.Program

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {T : Type*} [TopologicalSpace T] [T2Space T] [SecondCountableTopology T]
    [ChartedSpace E T] [IsManifold 𝓘(ℂ, E) ω T] [CompactSpace T]

local instance : ChartedSpace (E × V) (T × V) := prodChartedSpace E T V V

theorem b54_compact_projection_analytic
    (Z : Set (T × V)) (hZ : IsClosedAnalytic (E × V) Z) :
    IsClosedAnalytic V (Prod.snd '' Z) := by
  letI : IsManifold 𝓘(ℂ, E × V) ω (T × V) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod T V
  apply (an_manifold_isClosedAnalytic_iff _).mp
  apply an_remmert (an_manifoldSpace (E × V) (T × V)) (an_manifoldSpace V V)
    Prod.snd
  · refine ⟨isProperMap_snd_of_compactSpace, (an_manifold_isHom_iff _).mpr ?_⟩
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  · exact (an_manifold_isClosedAnalytic_iff _).mpr hZ

theorem b54_incidence_cone_algebraic (n : ℕ)
    (Z : Set (T × (Fin n → ℂ)))
    (hZ : @IsClosedAnalytic (E × (Fin n → ℂ)) _ _ (T × (Fin n → ℂ)) _
      (prodChartedSpace E T (Fin n → ℂ) (Fin n → ℂ)) Z)
    (hscale : ∀ (t : ℂ) (x : T) (v : Fin n → ℂ), (x, v) ∈ Z → (x, t • v) ∈ Z) :
    ∃ (m : ℕ) (d : Fin m → ℕ) (P : Fin m → MvPolynomial (Fin n) ℂ),
      (∀ i, (P i).IsHomogeneous (d i)) ∧
      Prod.snd '' Z = {v | ∀ i, MvPolynomial.eval v (P i) = 0} := by
  apply chow_cone_algebraic n (Prod.snd '' Z) (b54_compact_projection_analytic Z hZ)
  intro t v hv
  obtain ⟨⟨x, w⟩, hw, rfl⟩ := hv
  exact ⟨(x, t • w), hscale t x w hw, rfl⟩

end HodgeLean.Foundations.Program
