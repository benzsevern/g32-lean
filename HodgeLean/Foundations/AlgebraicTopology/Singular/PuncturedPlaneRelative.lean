import HodgeLean.Foundations.AlgebraicTopology.Singular.PuncturedPlaneLoop
import HodgeLean.Foundations.Program.SchoenTowerL1bActionWindingGenerator

/-! Relative degree compared with a specified logarithmic loop coefficient.
Source: Hatcher, Algebraic Topology (2002), §§2.1–2.2.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
open HodgeLean.Foundations.Program
namespace AlgebraicTopology.Singular.PuncturedPlane

theorem relativeDegree_of_lift
    {X : TopPair} (I F : X ⟶ pointComplementPair (0 : ℂ))
    (hI : Function.Injective (homologyMap ℤ 1 I.left))
    (p : C(UnitAddCircle, X.snd))
    (hpI : homologyMap ℤ 1 I.left
      (((SingularChainComplex ℤ X.snd).sc 1).moduleCatHomologyClass (loopCycle ℤ p)) =
      ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
        (loopCycle ℤ (windingCircle 0 1)))
    (L : ℝ → ℂ) (hL : Continuous L)
    (he : ∀ s : ℝ, Complex.exp (L s) = (F.left (p (s : UnitAddCircle))).val)
    (k : ℤ) (hk : ∀ s, L (s + 1) = L s + (k : ℂ) * (2 * Real.pi * Complex.I))
    (a : RelativeHomology ℤ X 2)
    (ha : relativeHomologyMap ℤ 2 I a = b6m_surfaceLocalClass ℤ (0 : ℂ))
    (ε : ℤ) (hf : relativeHomologyMap ℤ 2 F a = ε • b6m_surfaceLocalClass ℤ (0 : ℂ)) :
    k = ε := by
  let c := ((SingularChainComplex ℤ X.snd).sc 1).moduleCatHomologyClass (loopCycle ℤ p)
  let w := ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
    (loopCycle ℤ (windingCircle 0 1))
  have hF : homologyMap ℤ 1 F.left c = k • w := by
    have hn := b6m_homologyMap_loopCycle F.left.hom p
    apply hn.trans
    exact loopClass_of_lift (F.left.hom.comp p) L hL he k hk
  have hact (b : Homology ℤ X.snd 1) :
      homologyMap ℤ 1 F.left b = k • homologyMap ℤ 1 I.left b := by
    obtain ⟨n, hn⟩ := s2v_l1b_action_winding_class_smul_surjective (homologyMap ℤ 1 I.left b)
    have hb : n • c = b := hI (by rw [map_zsmul, hpI]; exact hn)
    rw [← hb, map_zsmul, map_zsmul, hF, hpI, smul_comm]
  apply s2v_l1b_action_plane_boundary_generator.1
  have hi := s2v_l1b_action_boundary_naturality ℤ I 1 a
  have hfi := s2v_l1b_action_boundary_naturality ℤ F 1 a
  rw [ha] at hi
  rw [hf, map_zsmul] at hfi
  have hd := hact ((b6m_relativeSingularBoundary ℤ X 1).hom a)
  rw [← hi] at hd
  exact hd.symm.trans hfi.symm

end AlgebraicTopology.Singular.PuncturedPlane
