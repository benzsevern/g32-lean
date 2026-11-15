import HodgeLean.Foundations.QuotientDuality.ProperCycleImageHeight
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingularComponentDimension

/-! # Actual smaller dimensions in the zero-residue-degree case -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Zero original residue degree forces the actual image component to have strictly smaller intrinsic dimension.
Source: Fulton, Intersection Theory, section 1.4; EGA IV, 5.6.5, the residue-field dimension formula.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_contracted_component_dimension
    {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (k : ℕ) (hdimX : TopologicalSpace.dim X.left = 2 * k)
    (ξ : X.left) (hcodim : Order.coheight ξ = k)
    (hzero : a1p_degree f.left ξ = 0) :
    ∃ m : ℕ, m < k ∧ topologicalKrullDim (cycleComponent Y.left (f.left ξ)) = (m : ℕ) := by
  have hx : Order.height ξ = (k : ℕ∞) := by
    have h := properCycle_middle_component_dimension X k hdimX ξ hcodim
    rw [topologicalKrullDim_cycleComponent] at h
    exact_mod_cast h
  obtain ⟨_, m, hm, _⟩ := a1d_height_eq_trdeg (f.left ξ)
  have hle := properCycle_height_image_le f ξ
  rw [hm, hx] at hle
  have hmk : m ≤ k := by exact_mod_cast hle
  have hne : m ≠ k := by
    intro heq
    have hp : 0 < a1p_degree f.left ξ := (a1p_degree_pos_iff f ξ).mpr (by rw [hm, hx, heq])
    rw [hzero] at hp
    exact Nat.not_lt_zero _ hp
  refine ⟨m, by omega, ?_⟩
  rw [topologicalKrullDim_cycleComponent, hm]
  rfl

end HodgeLean.Foundations.QuotientDuality
