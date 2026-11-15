import HodgeLean.Foundations.Program.G32Native.EulerModel.CoordinateHyperplaneClass
import HodgeLean.Foundations.Program.G32Native.EulerModel.ProjectiveCoordinateCohomology
import HodgeLean.Foundations.Program.G32Native.EulerModel.ProjectiveHyperplaneCycleTransport
import HodgeLean.Foundations.Program.SchoenCycleC2DeckTransportHelpers

/-! # Exact absolute normalization under the specified coordinate permutation -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Actual coordinate permutations identify the absolute classes of every pair of normalized literal residue-hyperplane coclasses with coefficient one. -/
theorem nativeResidueHyperplane_absolute_permutation (k : ℕ) (hk : 0 < k)
    (e : Equiv.Perm (Fin (k + 1))) (j : Fin (k + 1)) :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let I := s2e_s2b_residueIdeal k (e.symm j)
    let J := s2e_s2b_residueIdeal k j
    let jI := s2c_subschemeι PP I
    let jJ := s2c_subschemeι PP J
    ∃ (hI : IsIntegral (s2c_subscheme PP I).left),
      letI := hI
      ∃ (hJ : IsIntegral (s2c_subscheme PP J).left),
        letI := hJ
        ∀ (cI : s2e_supportedClass PP (s2e_componentCycle jI ℚ) 1)
          (cJ : s2e_supportedClass PP (s2e_componentCycle jJ ℚ) 1),
          a3b4_IsCycleClass PP.hom (s2e_componentCycle jI ℚ) 1 cI →
          a3b4_IsCycleClass PP.hom (s2e_componentCycle jJ ℚ) 1 cJ →
          s2e_classToAbsolute PP (s2e_componentCycle jI ℚ) 1 cI =
            s2e_classToAbsolute PP (s2e_componentCycle jJ ℚ) 1 cJ := by
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let I := s2e_s2b_residueIdeal k (e.symm j)
  let J := s2e_s2b_residueIdeal k j
  let jI := s2c_subschemeι PP I
  let jJ := s2c_subschemeι PP J
  let δ := (complexProjectiveCoordinateIso e).hom
  letI : IsIntegral PP.left := IntersectionProductScaf_projective_integral k
  letI : Smooth PP.hom := IntersectionProductScaf_projective_smooth k
  letI : IsProjective PP.hom := ⟨⟨⟨k, 𝟙 _, Category.id_comp _⟩⟩⟩
  obtain ⟨hI, hsmI, hcodI, _⟩ := nativeResidueHyperplane_class k hk (e.symm j)
  obtain ⟨hJ, _, _, _⟩ := nativeResidueHyperplane_class k hk j
  letI := hI
  letI := hJ
  letI : IsClosedImmersion jI.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  letI : IsClosedImmersion jJ.left := inferInstanceAs (IsClosedImmersion J.subschemeι)
  have hcodim : ∀ x ∈ (s2e_componentCycle jI ℚ).support, Order.coheight x = 1 := by
    intro x hx
    rw [s2e_componentCycle_support] at hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact hcodI
  obtain ⟨_, _, hcycle⟩ := projectiveCoordinateHyperplane_componentCycle k hk e j
  have htransport := s2e_componentCycle_absolute_deck_transport jI δ 1 ⊤
    (by intro x hx; trivial) (by infer_instance) hcodim
  change s2e_componentCycle (jI ≫ δ) ℚ = s2e_componentCycle jJ ℚ at hcycle
  rw [hcycle] at htransport
  refine ⟨hI, hJ, ?_⟩
  intro cI cJ hcI hcJ
  have ht := htransport cI cJ hcI hcJ
  have hf : s2e_pullback ℚ δ 2
      (s2e_classToAbsolute PP (s2e_componentCycle jI ℚ) 1 cI) =
        s2e_classToAbsolute PP (s2e_componentCycle jI ℚ) 1 cI :=
    complexProjectiveCoordinateIso_cohomology k 2 e _
  have hinv := s2e_pullback_inv_cancel δ 2
    (s2e_classToAbsolute PP (s2e_componentCycle jI ℚ) 1 cI)
  rw [hf] at hinv
  exact (ht.trans hinv).symm

#print axioms nativeResidueHyperplane_absolute_permutation
end HodgeLean.Foundations.Program.G32Native.EulerModel
