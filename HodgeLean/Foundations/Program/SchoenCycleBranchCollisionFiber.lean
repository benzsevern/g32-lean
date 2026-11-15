import HodgeLean.Foundations.Program.SchoenCycleTotalCollisionFiber
import HodgeLean.Foundations.Program.SchoenCycleInsertionImmersion

/-! # Singleton fibers of the actual marked branch composite -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual marked branch composite has a singleton underlying fiber
when the inserted point is a total collision.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Hartshorne, Algebraic Geometry, II.3. -/
theorem s2e_total_collision_branch_scheme_fiber
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] (n : ℕ)
    (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (n + 1) ⟶ T),
      (∀ σ, s2_permute Z (n + 1) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (y : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z (n + 1) i)
      (Point.map (s2c_branchInsertion Z n a) y) = a) :
    (s2c_branchInsertion Z n a ≫ γ).left ⁻¹'
      {(s2c_branchInsertion Z n a ≫ γ).left y.underlying} = {y.underlying} := by
  let q := s2c_branchInsertion Z n a
  letI : IsClosedImmersion q.left := s2e_branchInsertion_isClosedImmersion Z n a
  have H := s2e_total_collision_scheme_fiber Z B (n + 1) γ hγ hquot
    (Point.map q y) a hx
  ext z
  change γ.left (q.left z) = γ.left (q.left y.underlying) ↔ z = y.underlying
  constructor
  · intro hz
    have hz' : q.left z ∈ γ.left ⁻¹' {γ.left (Point.map q y).underlying} := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff, Point.underlying_map] using hz
    rw [H] at hz'
    apply q.left.isClosedEmbedding.injective
    simpa only [Set.mem_singleton_iff, Point.underlying_map] using hz'
  · rintro rfl
    rfl

#print axioms s2e_total_collision_branch_scheme_fiber
end HodgeLean.Foundations.Program
