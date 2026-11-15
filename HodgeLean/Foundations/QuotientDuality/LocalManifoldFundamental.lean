import HodgeLean.Foundations.QuotientDuality.LocalCompactGluing

/-! Fundamental classes for locally oriented spaces carrying real manifold charts. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

/-- Real manifold charts supply compact-support detection in the orientation degree.
Source: Hatcher, Algebraic Topology, Theorem 3.26 and Lemma 3.27. -/
theorem charted_fundamental_class (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (n : ℕ) [ChartedSpace (Fin n → ℝ) X] (o : LocalRationalOrientation X n) :
    ∃! c : Homology ℚ X n, ∀ x, localOrientation X n c x = o.generator x := by
  apply fundamental_class_of_compact_detection X n o
  intro A hA
  have hn : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  exact (j5c_compact_manifold_aux hn hA).2

#print axioms charted_fundamental_class
end HodgeLean.Foundations.QuotientDuality
