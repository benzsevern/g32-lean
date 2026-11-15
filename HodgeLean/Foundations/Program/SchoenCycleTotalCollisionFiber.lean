import HodgeLean.Foundations.Program.SchoenCycleComplexPointUnderlying
import HodgeLean.Foundations.Program.SchoenCycleStep1
import HodgeLean.Foundations.Program.SchoenCyclePowerPointStabilizer

/-! # The fiber over an actual total collision -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every coordinate permutation fixes a power point whose coordinates are equal.
Source: Schoen, Compositio Mathematica 65 (1988), §2, symmetric product construction. -/
theorem s2e_total_collision_permutation_fixed
    (Z : Over (Spec ↧ℂ)) (n : ℕ) (x : ComplexPoint (g3_power Z n))
    (a : ComplexPoint Z) (hx : ∀ i, Point.map (g3_proj Z n i) x = a)
    (σ : Equiv.Perm (Fin n)) : Point.map (s2_permute Z n σ) x = x := by
  apply s2e_power_hom_ext n
  intro i
  change (x ≫ s2_permute Z n σ) ≫ g3_proj Z n i = x ≫ g3_proj Z n i
  simp only [Category.assoc, s2_permute, s2_check_lift_proj]
  exact (hx (σ.symm i)).trans (hx i).symm

#print axioms s2e_total_collision_permutation_fixed

/-- The complex-point fiber of the retained quotient over a total collision is
 a singleton, using the original finite categorical quotient hypotheses.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_total_collision_complex_fiber
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsIntegral B.left] (n : ℕ)
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z n i) x = a)
    (y : ComplexPoint (g3_power Z n)) (hy : Point.map γ y = Point.map γ x) : y = x := by
  obtain ⟨σ, hσ⟩ := s2e_step1_finite_quotient_point_orbits (g3_power Z n) B
    (Equiv.Perm (Fin n)) (s2_permute Z n) (s2e_step1_permute_one Z n)
    (s2e_step1_permute_mul Z n) γ hγ hquot x y hy.symm
  exact hσ.symm.trans (s2e_total_collision_permutation_fixed Z n x a hx σ)

#print axioms s2e_total_collision_complex_fiber

/-- The actual scheme-theoretic quotient fiber has a singleton underlying set
at a total collision; the statement does not assert that its scheme structure is reduced.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Hartshorne, Algebraic Geometry, II.3, Jacobson density. -/
theorem s2e_total_collision_scheme_fiber
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsIntegral B.left] (n : ℕ)
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z n i) x = a) :
    γ.left ⁻¹' {γ.left x.underlying} = {x.underlying} := by
  let X := g3_power Z n
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  letI : IsClosedImmersion x.left := isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)
  have hcx : IsClosed ({x.underlying} : Set X.left) := by
    change IsClosed {x.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using x.left.isClosedMap {IsLocalRing.closedPoint ℂ}
      (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  have hcb : IsClosed ({γ.left x.underlying} : Set B.left) := by
    simpa only [Set.image_singleton] using γ.left.isClosedMap {x.underlying} hcx
  have hcf : IsClosed (γ.left ⁻¹' {γ.left x.underlying}) := hcb.preimage γ.left.continuous
  have hs : (γ.left ⁻¹' {γ.left x.underlying}) ∩ closedPoints X.left ⊆
      {x.underlying} := by
    intro y hy
    let yp : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom y hy.2) (by simp)
    have hyp : yp.underlying = y := pointOfClosedPoint_apply X.hom y hy.2 _
    have he : Point.map γ yp = Point.map γ x := by
      apply s2e_complex_point_eq_of_underlying_eq
      rw [Point.underlying_map, Point.underlying_map, hyp]
      exact hy.1
    have hp := s2e_total_collision_complex_fiber Z B n γ hγ hquot x a hx yp he
    exact hyp.symm.trans (congrArg Point.underlying hp)
  apply Set.Subset.antisymm
  · rw [← closure_inter_closedPoints hcf]
    exact closure_minimal hs hcx
  · intro y hy
    rcases hy with rfl
    rfl

#print axioms s2e_total_collision_scheme_fiber
end HodgeLean.Foundations.Program
