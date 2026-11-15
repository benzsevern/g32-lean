import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

theorem exists_generic_point_for_finite_paths (h : Module.finrank ℂ E = 1)
    {ι : Type} [Fintype ι] (γ : ι → ℝ → C)
    (hγ : ∀ i, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (γ i))
    (x : C) (a b : E) {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ v ∈ U, ∀ i, v ∉ b3Rest_img (γ i) x ∧
      v ∉ b3Rest_bad (γ i) x a ∧ v ∉ b3Rest_bad (γ i) x b := by
  classical
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let μ : Measure E := Measure.addHaar
  let A : Set E := ⋃ i, b3Rest_img (γ i) x ∪ b3Rest_bad (γ i) x a ∪ b3Rest_bad (γ i) x b
  have hnull : μ A = 0 := measure_iUnion_null fun i =>
    measure_union_null (measure_union_null (b3Rest_img_null μ h (hγ i) x)
      (b3Rest_bad_null μ h (hγ i) x a)) (b3Rest_bad_null μ h (hγ i) x b)
  have hsub : ¬ U ⊆ A := fun hs =>
    (hU.measure_pos μ hne).ne' (measure_mono_null hs hnull)
  obtain ⟨v, hv, hvA⟩ := Set.not_subset.mp hsub
  refine ⟨v, hv, fun i => ⟨?_, ?_, ?_⟩⟩
  · intro hi
    exact hvA (mem_iUnion.mpr ⟨i, Or.inl (Or.inl hi)⟩)
  · intro hi
    exact hvA (mem_iUnion.mpr ⟨i, Or.inl (Or.inr hi)⟩)
  · intro hi
    exact hvA (mem_iUnion.mpr ⟨i, Or.inr hi⟩)

end HodgeLean.Foundations.Curves.AbelTheorem
