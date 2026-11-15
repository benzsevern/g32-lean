import HodgeLean.Foundations.QuotientDuality.RetainedInitialOrientation

/-! Transport of retained initial orientations through an algebraic isomorphism. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

theorem retained_isomorphic_quotient_orientation
    (S : g32p_Supplier) (Y W₀ W : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral W₀.left] [IsProjective W₀.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ) (q : g3_power Y n ⟶ W₀) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
      ∑ i, v i = 0 → s2_action S Y a e n v σ ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y n ⟶ T),
      (∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
        ∑ i, v i = 0 → s2_action S Y a e n v σ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q ≫ u = f)
    (hdim : TopologicalSpace.dim Y.left = 1) (E : W₀ ≅ W) :
    ∃ (o : LocalRationalOrientation (TopCat.of (ComplexPoint W)) (2 * n))
      (c : Homology ℚ (TopCat.of (ComplexPoint W)) (2 * n)),
      ∀ x, localOrientation (TopCat.of (ComplexPoint W)) (2 * n) c x = o.generator x := by
  obtain ⟨_, o₀, c₀, _, _, hc₀⟩ := retained_initial_coherent_orientation
    S Y W₀ a e ha1 hamul n q hsurj hinv hquot hdim
  let H := Point.isoMapHomeomorph E
  obtain ⟨o, hc, _⟩ := homeomorph_pushforward_coherent_orientation
    (TopCat.of (ComplexPoint W₀)) (TopCat.of (ComplexPoint W)) (2 * n) o₀ c₀ hc₀ H
  exact ⟨o, homologyMap ℚ (2 * n) (TopCat.ofHom ⟨H, H.continuous⟩) c₀, hc⟩

#print axioms retained_isomorphic_quotient_orientation
end HodgeLean.Foundations.QuotientDuality
