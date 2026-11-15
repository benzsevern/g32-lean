import HodgeLean.Foundations.Curves.AbelTheorem.FiniteTransverseCrossings

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C]
attribute [local instance] b3Forms_isManifold_real

theorem exists_shift_avoiding_rational_path_vertices (γ : b3_SmoothLoop E C)
    {ι : Type} [Fintype ι] (δ : ι → ℝ → C)
    (hδ : ∀ i, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (δ i))
    (htr : ∀ i s t, γ.val s = δ i t →
      b3_orient E (b3_velocity E C γ.val s) (b3_velocity E C (δ i) t) ≠ 0) :
    ∃ a : ℝ, ∀ (N : ℕ) (k : ℤ) i t, t ∈ Icc (0 : ℝ) 1 →
      γ.val (k / N + a) ≠ δ i t := by
  classical
  let X : Set (ℝ × ℝ) := ⋃ i,
    {q | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ Icc (0 : ℝ) 1 ∧ γ.val q.1 = δ i q.2}
  have hX : X.Finite := Set.finite_iUnion fun i =>
    finite_transverse_crossings_in_box γ.val (δ i) γ.property.2 (hδ i) (htr i) 0 1 0 1
  let Bad : Set ℝ := ⋃ p ∈ X, Set.range (fun q : ℚ => p.1 - (q : ℝ))
  have hBad : Bad.Countable := hX.countable.biUnion fun p _ => Set.countable_range _
  obtain ⟨a, ha⟩ := (hBad.dense_compl ℝ).nonempty
  have ha' : ∀ p ∈ X, ∀ q : ℚ, p.1 - (q : ℝ) ≠ a := by
    intro p hp q he
    exact ha (he ▸ mem_iUnion₂.mpr ⟨p, hp, q, rfl⟩)
  refine ⟨a, ?_⟩
  intro N k i t ht he
  let v : ℝ := k / N + a
  have hp : (Int.fract v, t) ∈ X := mem_iUnion.mpr ⟨i,
    ⟨Int.fract_nonneg v, (Int.fract_lt_one v).le⟩, ht, by
      rw [b3Rest2_periodic_fract γ.property.1]
      exact he⟩
  apply ha' _ hp ((k : ℚ) / N - (⌊v⌋ : ℚ))
  simp only [Int.fract]
  push_cast
  dsimp only [v]
  ring

end HodgeLean.Foundations.Curves.AbelTheorem
