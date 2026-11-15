import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Rational singular cohomology of the finite categorical quotient is the invariant subspace.
Source: Bredon, Sheaf Theory, second edition, Chapter V, finite quotient comparison;
Schoen, Compositio Mathematica 65 (1988), printed p. 18. -/
theorem s2e_finite_quotient_rational_cohomology_comparison
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (S : Over (Spec ↧ℂ)) (f : X ⟶ S),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ S, q ≫ g = f)
    (n : ℕ) :
    ∃ e : Cohomology ℚ (TopCat.of (ComplexPoint Y)) n ≃ₗ[ℚ]
        (s2e_quotientCohomologyRepresentation X G a ha1 hamul n).invariants,
      ∀ c, (e c).val = s2e_pullback ℚ q n c := by
  let f := s2e_quotientPullbackToInvariants G a ha1 hamul q hinv n
  have hi : Function.Injective f := fun _ _ h =>
    s2e_chain_finite_quotient_pullback_injective_aux X Y G a ha1 hamul q hsurj hinv hquot n
      (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro b
    have hb (g : G) : s2e_pullback ℚ (a g) n b.val = b.val := by
      have h := b.property g⁻¹
      change s2e_pullback ℚ (a (g⁻¹)⁻¹) n b.val = b.val at h
      simpa only [inv_inv] using h
    obtain ⟨c, hc⟩ := s2e_finite_quotient_invariant_descent
      X Y G a ha1 hamul q hsurj hinv hquot n b.val hb
    exact ⟨c, Subtype.ext hc⟩
  exact ⟨LinearEquiv.ofBijective f ⟨hi, hs⟩, fun _ => rfl⟩

/-- The invariant comparison uses the actual scheme pullback on every rational class.
Source: Hatcher, Algebraic Topology, §3.1, naturality of singular cohomology;
Bredon, Sheaf Theory, second edition, Chapter V, finite quotient comparison. -/
theorem s2e_finite_quotient_rational_cohomology_comparison_pullback
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (S : Over (Spec ↧ℂ)) (f : X ⟶ S),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ S, q ≫ g = f)
    (n : ℕ) (c : Cohomology ℚ (TopCat.of (ComplexPoint Y)) n) :
    ((s2e_finite_quotient_rational_cohomology_comparison
      X Y G a ha1 hamul q hsurj hinv hquot n).choose c).val =
      s2e_pullback ℚ q n c :=
  (s2e_finite_quotient_rational_cohomology_comparison
    X Y G a ha1 hamul q hsurj hinv hquot n).choose_spec c

end HodgeLean.Foundations.Program
