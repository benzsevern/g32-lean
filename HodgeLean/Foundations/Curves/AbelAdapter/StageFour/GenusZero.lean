import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.TorusOperations
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.PeriodFormDuality
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.AnalyticFactor

noncomputable section
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped TensorProduct Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Source: Forster, Lectures on Riemann Surfaces, §21, the period quotient. -/
theorem jacobian_subsingleton_of_no_forms (h : Module.finrank ℂ E = 1)
    [Subsingleton (b3_HolForm E C)] : Subsingleton (b3_Jacobian E C) := by
  haveI : Subsingleton (b3Rest2_QJ E C) :=
    (periodQuotientDualEquiv (E := E) (C := C) h).injective.subsingleton
  refine ⟨fun x y ↦ ?_⟩
  induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
      exact congrArg (fun q : b3Rest2_QJ E C ↦
        (QuotientAddGroup.mk q : b3_Jacobian E C)) (Subsingleton.elim a b)


/-- Source: Forster, Lectures on Riemann Surfaces, §21, universal property of the Jacobian. -/
theorem torusMap_eq_zero_of_no_forms (h : Module.finrank ℂ E = 1)
    [Subsingleton (b3_HolForm E C)]
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (M : Type) [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M]
    (G : Submodule ℂ (ℂ ⊗[ℤ] M)) (hG : b2_IsWeightOne M G)
    [DiscreteTopology (b2_latticeMap M G).range]
    (p : C) (f : C → b2_torus M G)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, b5_V M G) ω f) (hp : f p = 0) :
    ∀ x, f x = 0 := by
  letI := jacobian_subsingleton_of_no_forms (E := E) (C := C) h
  obtain ⟨H, ⟨_, hH⟩, _⟩ := analyticTorusFactor h M G hG p f hf hp
  intro x
  exact (hH x).symm.trans
    ((congrArg H (Subsingleton.elim (analyticAbel (E := E) (C := C) h p x) 0)).trans
      (map_zero H))



/-- Source: Forster, Lectures on Riemann Surfaces, §21, universal property of the Jacobian. -/
theorem torusMap_constant_of_no_forms (h : Module.finrank ℂ E = 1)
    [Subsingleton (b3_HolForm E C)]
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (M : Type) [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M]
    (G : Submodule ℂ (ℂ ⊗[ℤ] M)) (hG : b2_IsWeightOne M G)
    [DiscreteTopology (b2_latticeMap M G).range]
    (p : C) (f : C → b2_torus M G)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, b5_V M G) ω f) :
    ∀ x, f x = f p := by
  have hn := torusMap_eq_zero_of_no_forms (E := E) (C := C) h M G hG p
    (fun x ↦ f x - f p)
    (torus_sub_contMDiff G f (fun _ ↦ f p) hf contMDiff_const) (sub_self (f p))
  exact fun x ↦ sub_eq_zero.mp (hn x)


end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
