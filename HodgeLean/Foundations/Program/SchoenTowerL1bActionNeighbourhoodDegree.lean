import HodgeLean.Foundations.AlgebraicTopology.Singular.PuncturedPlaneRelative
import HodgeLean.Foundations.Program.SchoenTowerL1bActionDeckHomology

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- An injective chart inclusion on H₁ compares the logarithmic coefficient
of a source generator loop with the relative local degree. -/
theorem s2v_l1b_action_neighbourhood_deck_degree
    {X : TopPair} (I F : X ⟶ pointComplementPair (0 : ℂ))
    (hI : Function.Injective (homologyMap ℤ 1 I.left))
    (p : C(UnitAddCircle, X.snd))
    (hpI : homologyMap ℤ 1 I.left
      (((SingularChainComplex ℤ X.snd).sc 1).moduleCatHomologyClass (loopCycle ℤ p)) =
      ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
        (loopCycle ℤ (s2v_l1b_action_windingCircleMap 0 1)))
    (L : ℝ → ℂ) (hL : Continuous L)
    (he : ∀ s : ℝ, Complex.exp (L s) = (F.left (p (s : UnitAddCircle))).val)
    (k : ℤ) (hk : ∀ s, L (s + 1) = L s + (k : ℂ) * (2 * Real.pi * Complex.I))
    (a : RelativeHomology ℤ X 2)
    (ha : relativeHomologyMap ℤ 2 I a = b6m_surfaceLocalClass ℤ (0 : ℂ))
    (ε : ℤ) (hf : relativeHomologyMap ℤ 2 F a = ε • b6m_surfaceLocalClass ℤ (0 : ℂ)) :
    k = ε := by
  exact PuncturedPlane.relativeDegree_of_lift I F hI p hpI L hL he k hk a ha ε hf

end HodgeLean.Foundations.Program
