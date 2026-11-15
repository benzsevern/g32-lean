import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.ThetaForms

/-! # Normalized differential of the period cover

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations.Program Filter
open scoped Manifold ContDiff TensorProduct Topology
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

/-- The period cover has identity derivative in the retained torus charts.
Source: Birkenhake–Lange, §§1.1–1.2; b3A_torus_chart_mk.
HC no distance; AV milestone no distance. -/
theorem torusCover_mfderiv {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    [DiscreteTopology (b2_latticeMap Λ F).range] (z : b3A_TM F) :
    mfderiv 𝓘(ℂ, b3A_TM F) 𝓘(ℂ, b3A_TM F) (b2_torusCover Λ F) z =
      ContinuousLinearMap.id ℂ (b3A_TM F) := by
  have hm := (b2_torusCover_contMDiff F).mdifferentiable (by simp) z
  rw [hm.mfderiv_abuse]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
    PartialEquiv.refl_symm, PartialEquiv.refl_coe, Function.comp_id,
    ModelWithCorners.range_eq_univ, Set.range_id, fderivWithin_univ, extChartAt_coe,
    modelWithCornersSelf_coe, Function.id_comp, id_eq]
  obtain ⟨a, ha⟩ := b3A_torus_chart_mk F
    ((b2_coordHomeomorph Λ F).symm.continuous.continuousAt) (u₀ := z)
  have he : (chartAt (b3A_TM F) (b2_torusCover Λ F z) ∘ b2_torusCover Λ F) =ᶠ[𝓝 z]
      (fun u ↦ u + a) := by
    filter_upwards [ha] with u hu
    change chartAt (b3A_TM F) (QuotientAddGroup.mk ((b2_coordHomeomorph Λ F).symm z))
      (QuotientAddGroup.mk ((b2_coordHomeomorph Λ F).symm u)) = u + a
    rw [hu]
    exact congrArg (· + a) ((b2_coordHomeomorph Λ F).apply_symm_apply u)
  rw [he.fderiv_eq]
  simp only [fderiv_add_const, fderiv_id']

/-- A local lift through the retained period cover has the same tangent derivative as its projection.
Source: Birkenhake–Lange, §§1.1–1.2; mfderiv_comp and torusCover_mfderiv.
HC no distance; AV milestone no distance. -/
theorem torusCover_lift_mfderiv
    {U M : Type} [NormedAddCommGroup U] [NormedSpace ℂ U]
    [TopologicalSpace M] [ChartedSpace U M]
    {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    [DiscreteTopology (b2_latticeMap Λ F).range]
    (f : M → b2_torus Λ F) (g : M → b3A_TM F) (x : M)
    (hg : MDifferentiableAt 𝓘(ℂ, U) 𝓘(ℂ, b3A_TM F) g x)
    (he : f =ᶠ[𝓝 x] b2_torusCover Λ F ∘ g) :
    mfderiv 𝓘(ℂ, U) 𝓘(ℂ, b3A_TM F) f x =
      mfderiv 𝓘(ℂ, U) 𝓘(ℂ, b3A_TM F) g x := by
  rw [he.mfderiv_eq, mfderiv_comp x
    ((b2_torusCover_contMDiff F).mdifferentiable (by simp) (g x)) hg,
    torusCover_mfderiv]
  apply ContinuousLinearMap.ext
  intro v
  rfl

#print axioms torusCover_mfderiv
#print axioms torusCover_lift_mfderiv

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
