import HodgeLean.Foundations.Program.SchoenCycleU1SupportSeparation
import HodgeLean.Foundations.Program.SchoenCycleU1QuotientNeighbourhood
import HodgeLean.Foundations.Program.SchoenCycleU1DivisorCoordinates

/-! # Retained polynomial charts separating distinct divisor support points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Any finite tuple on the retained curve has one affine neighbourhood and
one regular section whose values identify precisely its distinct support points.
Source: Hartshorne, Algebraic Geometry, II.2, affine regular functions;
`s2e_u1_exists_affine_open_containing_support`. -/
theorem s2e_u1_tuple_separating_affine_section
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (N : ℕ) (x : Fin N → ComplexPoint Z) :
    ∃ U : Z.left.Opens, IsAffineOpen U ∧ (∀ i, (x i).underlying ∈ U) ∧
      ∃ t : Γ(Z.left, U), ∀ i j,
        Point.evaluate U t (x i) = Point.evaluate U t (x j) ↔ x i = x j := by
  classical
  let S : Finset (ComplexPoint Z) := Finset.univ.image x
  obtain ⟨U, hUa, hU⟩ := s2e_u1_exists_affine_open_containing_support Z
    (S.image Point.underlying)
  have hS : ∀ y ∈ S, y.underlying ∈ U := by
    intro y hy
    exact hU _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  obtain ⟨t, ht⟩ := s2e_u1_affine_support_separating_section Z U hUa S hS
  have hx (i : Fin N) : x i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  refine ⟨U, hUa, (fun i => hS _ (hx i)), t, ?_⟩
  intro i j
  exact ⟨fun h => ht (hx i) (hx j) h, fun h => congrArg _ h⟩

/-- The actual retained quotient has an affine polynomial chart around any
ordered divisor with one regular coordinate separating its distinct support.
Its pullback remains the product with every multiplicity.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, third edition, I.1;
ACGH, Geometry of Algebraic Curves I, Chapter I, divisor coefficient charts. -/
theorem s2e_u1_retained_support_separating_polynomial_chart
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsProjective Z.hom] [IsIntegral B.left] [Smooth B.hom]
    (N : ℕ) (γ : g3_power Z N ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z N ⟶ T),
      (∀ σ, s2_permute Z N σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : Fin N → ComplexPoint Z) :
    ∃ U : Z.left.Opens, IsAffineOpen U ∧ (∀ i, (x i).underlying ∈ U) ∧
      ∃ t : Γ(Z.left, U),
        (∀ i j, Point.evaluate U t (x i) = Point.evaluate U t (x j) ↔ x i = x j) ∧
        ∃ V : B.left.Opens, IsAffineOpen V ∧
          (Point.map γ (s2_lift N x)).underlying ∈ V ∧
          ∃ hVU : γ.left ⁻¹ᵁ V ≤ s2e_u1_powerOpen Z N U,
            ∃! Q : Polynomial Γ(B.left, V), Q.map (γ.left.app V).hom =
              ∏ i : Fin N, (Polynomial.X - Polynomial.C
                (s2e_u1_coordinateSection Z B N γ U V hVU t i)) := by
  obtain ⟨U, hUa, hx, t, ht⟩ := s2e_u1_tuple_separating_affine_section Z N x
  have hpow : Point.underlying (s2_lift N x) ∈ s2e_u1_powerOpen Z N U := by
    apply (s2e_u1_mem_powerOpen Z N U _).mpr
    intro i
    have he : Point.map (g3_proj Z N i) (s2_lift N x) = x i := by
      simp only [Point.map, s2_check_lift_proj]
    simpa only [← Point.underlying_map, he] using hx i
  obtain ⟨V, hVa, hb, hVU⟩ := s2e_u1_quotient_affine_chart_inside_invariant_open
    Z B N γ hsurj hγ hquot (s2e_u1_powerOpen Z N U)
    (s2e_u1_powerOpen_permute Z N U) (s2_lift N x) hpow
  exact ⟨U, hUa, hx, t, ht, V, hVa, hb, hVU,
    s2e_u1_retained_divisor_coordinate_polynomial Z B N γ hsurj hγ hquot U V hVa hVU t⟩

end HodgeLean.Foundations.Program
