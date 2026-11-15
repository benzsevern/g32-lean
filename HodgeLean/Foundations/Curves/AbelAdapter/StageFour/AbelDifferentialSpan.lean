import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.BasisSelection
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.AbelInvariantDifferential
import HodgeLean.Foundations.Curves.AbelAdapter.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [Module.Finite ℤ (b3_periodLattice E C)]
  [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]

theorem covector_eq_zero_of_abelDifferential (h : Module.finrank ℂ E = 1) (p : C)
    (L : b3Rest2_VJ E C →L[ℂ] ℂ)
    (hL : ∀ q v, L (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) (analyticAbel h p) q v) = 0) :
    L = 0 := by
  obtain ⟨θ, hθL⟩ := (periodFormEquiv (C := C) h).surjective L
  have hθ : θ = 0 := by
    apply Subtype.ext
    funext v
    have heval := abelJacobi_invariant_differential h p (analyticAbel h p)
      (b3_exists_abelJacobi (C := C) h p).choose_spec θ v.1 v.2
    have hc : periodLinear θ = L := (periodFormEquiv_apply h θ).symm.trans hθL
    exact heval.symm.trans ((congrArg (fun ℓ : b3Rest2_VJ E C →L[ℂ] ℂ ↦
      ℓ (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) (analyticAbel h p) v.1 v.2)) hc).trans
        (hL v.1 v.2))
  exact hθL.symm.trans ((congrArg (periodFormEquiv h) hθ).trans (map_zero _))


theorem abelDifferential_span (h : Module.finrank ℂ E = 1) (p : C) :
    Submodule.span ℂ (Set.range fun s : C × E ↦
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) (analyticAbel h p) s.1 s.2) = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply bot_unique
  intro L hL
  change L = 0
  have hz := covector_eq_zero_of_abelDifferential h p
    (LinearMap.toContinuousLinearMap L) (fun q v ↦
      (Submodule.mem_dualAnnihilator L).mp hL _
        (Submodule.subset_span ⟨(q, v), rfl⟩))
  exact LinearMap.ext fun w ↦ congrArg (fun ℓ : b3Rest2_VJ E C →L[ℂ] ℂ ↦ ℓ w) hz

theorem finite_abelDifferential_basis (h : Module.finrank ℂ E = 1) (p : C) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (b3Rest2_VJ E C)) (w : Fin n → C × E),
      ∀ i, b i = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C)
        (analyticAbel h p) (w i).1 (w i).2 :=
  basis_of_spanning_range (k := ℂ) (V := b3Rest2_VJ E C) (T := C × E)
    (fun s : C × E ↦ mfderiv 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) (analyticAbel h p) s.1 s.2)
    (abelDifferential_span h p)

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
