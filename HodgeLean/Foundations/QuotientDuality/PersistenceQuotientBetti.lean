import HodgeLean.Foundations.Program.SchoenTransferQ3OrbitInjective
import HodgeLean.Foundations.Program.SchoenCycleStep1
import HodgeLean.Foundations.Program.SchoenCycleRetainedAction
import HodgeLean.RealDefs.FiniteBettiCompact
import HodgeLean.Foundations.QuotientDuality.OrientationLinearDescent

/-! Finite rational homology of the initial retained quotient. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_finite_quotient_homology
    (X W : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    (G : Type) [Group G] [Fintype G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ W) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      (∀ u, a u ≫ f = f) → ∃! u : W ⟶ T, q ≫ u = f)
    (n : ℕ) : Module.Finite ℚ (Homology ℚ (TopCat.of (ComplexPoint W)) n) := by
  letI : Surjective q.left := s2e_step1_surjective_of_complexPoint_surjective X W q hsurj
  have horbit := s2e_step1_finite_quotient_point_orbits X W G a ha1 hamul q hinv hquot
  have hi := s4_q3_orbit_pullback_injective X W G a ha1 hamul q hsurj hinv horbit n
  letI : Module.Finite ℚ (Homology ℚ (TopCat.of (ComplexPoint X)) n) :=
    finbetti_finiteHomology_of_compact (Fin (dim X.left) → ℂ) n
  exact Module.Finite.of_surjective _
    (homology_surjective_of_cohomology_injective (TopCat.ofHom (Point.continuousMap q)) n hi)

lemma persistence_initial_quotient_homology
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (N : ℕ) (q : g3_power Y N ⟶ W) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ (v : Fin N → ZMod S.m) (τ : Equiv.Perm (Fin N)),
      ∑ t, v t = 0 → s2_action S Y a e N v τ ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y N ⟶ T),
      (∀ (v : Fin N → ZMod S.m) (τ : Equiv.Perm (Fin N)),
        ∑ t, v t = 0 → s2_action S Y a e N v τ ≫ f = f) →
      ∃! u : W ⟶ T, q ≫ u = f)
    (n : ℕ) : Module.Finite ℚ (Homology ℚ (TopCat.of (ComplexPoint W)) n) := by
  obtain ⟨h1, hmul⟩ := s2e_retainedAction_laws S Y a e ha1 hamul N
  apply persistence_finite_quotient_homology (g3_power Y N) W
    (s2e_Retained S.m N) (s2e_retainedAction S Y a e N) h1 hmul q hsurj
  · intro g
    exact hinv g.vector g.perm g.zero_sum
  · intro T f hf
    apply hquot T f
    intro v τ hv
    exact hf ⟨v, hv, τ⟩

end HodgeLean.Foundations.QuotientDuality
