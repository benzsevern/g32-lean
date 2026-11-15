import HodgeLean.Foundations.Program.SchoenTowerL1bActionNeighbourhoodDegree

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A logarithmic deck coefficient multiplies every relative class of the
source neighbourhood under its map to the plane pair. -/
theorem s2v_l1b_action_neighbourhood_relative_action
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
    (a : RelativeHomology ℤ X 2) :
    relativeHomologyMap ℤ 2 F a = k • relativeHomologyMap ℤ 2 I a := by
  let c := ((SingularChainComplex ℤ X.snd).sc 1).moduleCatHomologyClass (loopCycle ℤ p)
  let w := ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
    (loopCycle ℤ (s2v_l1b_action_windingCircleMap 0 1))
  have hF : homologyMap ℤ 1 F.left c = k • w := by
    have hn := b6m_homologyMap_loopCycle F.left.hom p
    apply hn.trans
    exact s2v_l1b_action_circle_loop_class_of_lift (F.left.hom.comp p) L hL he k hk
  have hact (b : Homology ℤ X.snd 1) :
      homologyMap ℤ 1 F.left b = k • homologyMap ℤ 1 I.left b := by
    obtain ⟨n, hn⟩ := s2v_l1b_action_winding_class_smul_surjective (homologyMap ℤ 1 I.left b)
    have hb : n • c = b := hI (by rw [map_zsmul, hpI]; exact hn)
    rw [← hb, map_zsmul, map_zsmul, hF, hpI, smul_comm]
  letI : ContractibleSpace (pointComplementPair (0 : ℂ)).fst := by
    change ContractibleSpace ℂ
    infer_instance
  apply (s2v_l1b_action_boundary_sign_iff ℤ F a
    (relativeHomologyMap ℤ 2 I a) k).mpr
  rw [s2v_l1b_action_boundary_naturality]
  exact hact _

end HodgeLean.Foundations.Program
