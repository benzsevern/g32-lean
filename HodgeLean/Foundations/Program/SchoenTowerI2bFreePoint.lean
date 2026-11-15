import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Separation.Basic

/-! Free points for the retained cyclic curve action.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A nonempty space with complex one-dimensional charts has infinitely many points.
Source: every chart target contains a complex neighborhood. -/
theorem s2v_i2b_charted_curve_infinite
    (C : Type*) [TopologicalSpace C] [ChartedSpace ℂ C] [Nonempty C] : Infinite C := by
  classical
  by_contra h
  haveI : Finite C := not_infinite_iff_finite.mp h
  let x : C := Classical.choice inferInstance
  have hi : (chartAt ℂ x).target.Infinite :=
    infinite_of_mem_nhds (chartAt ℂ x x) (chart_target_mem_nhds ℂ x)
  have hs : (chartAt ℂ x).target ⊆ Set.range (chartAt ℂ x) := by
    intro z hz
    exact ⟨(chartAt ℂ x).symm z, (chartAt ℂ x).right_inv hz⟩
  exact hi ((Set.finite_range (chartAt ℂ x)).subset hs)

/-- A finite curve action with only finitely many branch orbits has a free point.
Source: finiteness of each orbit and infinitude of the curve. -/
theorem s2v_i2b_exists_free_point
    {G C Z ι : Type*} [Group G] [Finite G] [MulAction G C] [Infinite C] [Finite ι]
    (f : C → Z) (y : ι → C)
    (horbit : ∀ x z : C, f x = f z ↔ ∃ g : G, g • x = z)
    (hbranch : ∀ z : C, MulAction.stabilizer G z ≠ ⊥ ↔ ∃ t, f z = f (y t)) :
    ∃ z : C, MulAction.stabilizer G z = ⊥ := by
  obtain ⟨z, hz⟩ := (Set.finite_range (fun p : ι × G => p.2 • y p.1)).exists_notMem
  refine ⟨z, ?_⟩
  by_contra h
  obtain ⟨t, ht⟩ := (hbranch z).mp h
  obtain ⟨g, hg⟩ := (horbit (y t) z).mp ht.symm
  exact hz ⟨(t, g), hg⟩

/-- The orbit map at a point with trivial stabilizer is injective.
Source: the stabilizer criterion for equality of two translates. -/
theorem s2v_i2b_orbitMap_injective
    {G C : Type*} [Group G] [MulAction G C] (z : C)
    (hz : MulAction.stabilizer G z = ⊥) : Function.Injective (fun g : G => g • z) := by
  intro g k he
  change g • z = k • z at he
  have hmem : k⁻¹ * g ∈ MulAction.stabilizer G z := by
    change (k⁻¹ * g) • z = z
    rw [mul_smul, he, inv_smul_smul]
  rw [hz, Subgroup.mem_bot] at hmem
  exact (inv_mul_eq_one.mp hmem).symm

end HodgeLean.Foundations.Program
