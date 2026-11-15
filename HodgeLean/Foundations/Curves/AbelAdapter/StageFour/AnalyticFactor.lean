import HodgeLean.Foundations.Curves.AbelAdapter.Defs
import HodgeLean.Foundations.AnalyticAlbanese.Basic

noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program HodgeLean.Foundations.AnalyticAlbanese
open scoped TensorProduct Manifold ContDiff CategoryTheory.MonObj
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

theorem analyticTorusFactor (h : Module.finrank ℂ E = 1)
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (M : Type) [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M]
    (G : Submodule ℂ (ℂ ⊗[ℤ] M)) (hG : b2_IsWeightOne M G)
    [DiscreteTopology (b2_latticeMap M G).range]
    (p : C) (f : C → b2_torus M G)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, b5_V M G) ω f) (hp : f p = 0) :
    ∃! H : b3_Jacobian E C →+ b2_torus M G,
      ContMDiff 𝓘(ℂ, b5_V (b3_periodLattice E C) (b3_periodF E C))
        𝓘(ℂ, b5_V M G) ω H ∧ ∀ x, H (analyticAbel h p x) = f x := by
  obtain ⟨L, ⟨hL, hpath⟩, _⟩ := period_lift E C h M G hG p f hf hp
  have hD := factorization_unique E C h M G hG p f hf hp
    (analyticAbel h p) (b3_exists_abelJacobi (C := C) h p).choose_spec L hL hpath
  exact ⟨descend (b3_periodF E C) G L hL,
    ⟨(descent_holomorphic _ _ _ _ L hL).1, hD.1⟩,
    fun H hH ↦ hD.2 H hH.1 hH.2⟩


theorem analyticAbelianFactor (h : Module.finrank ℂ E = 1)
    [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (p : C) (f : C → ComplexPoint A)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin (TopologicalSpace.dim A.left) → ℂ) ω f)
    (hp : f p = 1) :
    ∃ H : b3_Jacobian E C →+ Additive (ComplexPoint A),
      ContMDiff 𝓘(ℂ, b5_V (b3_periodLattice E C) (b3_periodF E C))
        𝓘(ℂ, Fin (TopologicalSpace.dim A.left) → ℂ) ω (fun t ↦ Additive.toMul (H t)) ∧
      ∀ x, H (analyticAbel h p x) = Additive.ofMul (f x) := by
  classical
  letI := b2_latticeMap_discrete (b2_abelianF A) (b2_abelianF_isWeightOne A)
  let e := AddEquiv.ofBijective (b2_abelianToPoint A) (b2_abelianToPoint_bijective A)
  let f' : C → b2_torus (b2_abelianLattice A) (b2_abelianF A) :=
    fun x ↦ e.symm (Additive.ofMul (f x))
  have hf' : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, b5_V (b2_abelianLattice A) (b2_abelianF A)) ω f' :=
    (b2_abelianToPoint_symm_contMDiff A).comp hf
  have hp' : f' p = 0 := by
    exact (congrArg e.symm (congrArg
      (Additive.ofMul : ComplexPoint A → Additive (ComplexPoint A)) hp)).trans
      (map_zero e.symm)
  obtain ⟨D, ⟨hD, hDf⟩, _⟩ := analyticTorusFactor h
    (b2_abelianLattice A) (b2_abelianF A) (b2_abelianF_isWeightOne A) p f' hf' hp'
  refine ⟨(b2_abelianToPoint A).comp D,
    (b2_abelianToPoint_contMDiff A).comp hD, ?_⟩
  intro x
  exact (congrArg e (hDf x)).trans (e.apply_symm_apply _)

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
