import HodgeLean.Foundations.QuotientDuality.LocalOrientationOfGlobal
import HodgeLean.Foundations.QuotientDuality.OrientationRelativeDescent
import HodgeLean.Foundations.QuotientDuality.OrientationGeneration
import HodgeLean.Foundations.QuotientDuality.OrientationScaling
import HodgeLean.Foundations.QuotientDuality.OrientationLocalReduction

/-! Coherent quotient orientations from the actual rational orbit pushforward. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem quotient_coherent_orientation
    (G : Type) [Group G] [Fintype G] (X : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] [T2Space X] [PseudoMetrizableSpace X]
    [T2Space (orbitSpace G X)] [PseudoMetrizableSpace (orbitSpace G X)]
    (hX : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hY : ∀ (x : orbitSpace G X) (U : Opens (orbitSpace G X)), x ∈ U →
      ∃ V : Opens (orbitSpace G X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℕ) (cX : Homology ℚ X n)
    (hlocal : ∀ x, Function.Bijective (orientationLine X n cX x))
    (hvanish : ∀ x i, i ≠ n → Subsingleton (orientationGroup X i x))
    (hpreserve : ∀ g : G, homologyMap ℚ n (deckMap G X g) cX = cX)
    (d : ℕ) (hd : 0 < d) :
    ∃ (oY : LocalRationalOrientation (orbitSpace G X) n)
      (cY : Homology ℚ (orbitSpace G X) n),
      homologyMap ℚ n (orbitMap G X) cX = (d : ℚ) • cY ∧
      ∀ y, localOrientation (orbitSpace G X) n cY y = oY.generator y := by
  have hgen : ∀ y, Function.Bijective (orientationLine (orbitSpace G X) n
      (homologyMap ℚ n (orbitMap G X) cX) y) := by
    intro y
    obtain ⟨hlift, hker⟩ := orbit_relative_descent G X hX hY y n
    exact quotient_pushforward_local_generators_of_relative_descent G X n cX
      hlocal hpreserve y hlift hker
  obtain ⟨cY, hdegree, hcY⟩ := normalized_pushforward_generators G X n cX d hd hgen
  have hv : ∀ y i, i ≠ n → Subsingleton (orientationGroup (orbitSpace G X) i y) := by
    intro y i hi
    letI := orbit_relative_vanishes G X y n i hi hvanish
    obtain ⟨hlift, _⟩ := orbit_relative_descent G X hX hY y i
    refine ⟨fun u v => ?_⟩
    obtain ⟨c, hc, _⟩ := hlift u
    obtain ⟨e, he, _⟩ := hlift v
    exact hc.symm.trans ((congrArg
      (relativeHomologyMap ℚ i (orbitComplementPairMap G X y))
      (Subsingleton.elim c e)).trans he)
  exact ⟨localOrientationOfGlobal (orbitSpace G X) n cY hcY hv,
    cY, hdegree, fun _ => rfl⟩

#print axioms quotient_coherent_orientation
end HodgeLean.Foundations.QuotientDuality
