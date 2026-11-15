import HodgeLean.Foundations.Program.SchoenCycleBranchGeneratorJetUnit
import HodgeLean.Foundations.Program.SchoenCycleInsertionOrbitIdeal
import HodgeLean.Foundations.Program.SchoenCycleInvariantIdealSections
import HodgeLean.Foundations.Program.SchoenCycleQuotientIdealJets
import HodgeLean.Foundations.Program.SchoenCycleMarkedProductStabilizer
import HodgeLean.Foundations.Program.SchoenCyclePowerPointStabilizer

/-! # Actual branch sections with prescribed marked-product jets -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- Every finite jet of the actual marked parameter product is represented by a section of the actual retained branch ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_branchIdeal_marked_product_jet_descent
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (n + 1) ⟶ T),
      (∀ σ, s2_permute Z (n + 1) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z (n + 1))) (a : ComplexPoint Z)
    (S : Finset (Fin (n + 1)))
    (hS : ∀ i, i ∈ S ↔ Point.map (g3_proj Z (n + 1) i) x = a)
    (U : B.left.affineOpens) (hxU : γ.left x.underlying ∈ U.1) (N : ℕ) :
    ∃ c ∈ (s2c_branchIdeal Z B n γ a).ideal U,
      γ.left.stalkMap x.underlying
          (B.left.presheaf.germ U.1 (γ.left x.underlying) hxU c) -
        (∏ i ∈ S, s2e_curvePowerParameter Z (n + 1) x i) ∈
          IsLocalRing.maximalIdeal ((g3_power Z (n + 1)).left.presheaf.stalk x.underlying) ^ N := by
  let X := g3_power Z (n + 1)
  let G := Equiv.Perm (Fin (n + 1))
  let H := s2e_powerPointStabilizer Z (n + 1) x
  let W : X.left.affineOpens := ⟨γ.left ⁻¹ᵁ U.1, U.2.preimage γ.left⟩
  let I := s2e_insertionOrbitIdeal Z n a
  let J := I.ideal W
  let P := ∏ i ∈ S, s2e_curvePowerParameter Z (n + 1) x i
  have hx : ⊤ ≤ x.left ⁻¹ᵁ W.1 := s2e_step1_point_preimage X x W.1 hxU
  letI : IsClosedImmersion (x.left ≫ X.hom) := by
    rw [Over.w x]
    change IsClosedImmersion (𝟙 (Spec ↧ℂ))
    infer_instance
  letI : IsClosedImmersion x.left := IsClosedImmersion.of_comp x.left X.hom
  have hclosed : IsClosed ({x.underlying} : Set X.left) := by
    change IsClosed {x.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using x.left.isClosedMap {IsLocalRing.closedPoint ℂ}
      (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  have hJ : letI := s2e_step1_sectionAlgebra X W.1
      letI := s2e_step1_sectionAction X B G (s2_permute Z (n + 1))
        (s2e_step1_permute_one Z (n + 1)) (s2e_step1_permute_mul Z (n + 1)) γ hγ U.1
      letI := s2e_step1_sectionAction_smulComm X B G (s2_permute Z (n + 1))
        (s2e_step1_permute_one Z (n + 1)) (s2e_step1_permute_mul Z (n + 1)) γ hγ U.1
      ∀ σ, ∀ s ∈ J, (MulSemiringAction.toAlgAut G ℂ Γ(X.left, W.1)) σ s ∈ J := by
    intro σ s hs
    let u := s2_permute Z (n + 1) σ⁻¹
    letI : IsIso u := s2e_step1_action_isIso X G (s2_permute Z (n + 1))
      (s2e_step1_permute_one Z (n + 1)) (s2e_step1_permute_mul Z (n + 1)) σ⁻¹
    exact s2e_invariant_ideal_section_pullback I u.left
      (s2e_insertionOrbitIdeal_map_permute Z n a σ⁻¹) W
      (s2e_step1_action_preimage X B γ u (hγ σ⁻¹) U.1) s hs
  obtain ⟨c, hcJ, hc⟩ := s2e_quotient_invariant_stalk_ideal_jet_descent X B G
    (s2_permute Z (n + 1)) (s2e_step1_permute_one Z (n + 1))
    (s2e_step1_permute_mul Z (n + 1)) γ hγ hquot U.1 U.2 H x hx hclosed
    (fun _ => Iff.rfl) J hJ N P
    (s2e_marked_product_mem_insertionOrbitIdeal_stalk Z n a x S hS W hxU)
    (by
      intro σ hσ
      rw [s2e_marked_parameter_product_stabilizer_invariant Z (n + 1) x a S hS σ hσ,
        sub_self]
      exact Ideal.zero_mem _)
  refine ⟨c, s2e_branchIdeal_mem_of_pullback_mem_insertionOrbitIdeal Z B n γ a U c hcJ, ?_⟩
  rw [γ.left.germ_stalkMap_apply U.1 x.underlying hxU]
  exact hc

/-- An actual branch section pulls back to the marked parameter product times a local unit, with every other collision block retained.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_branchIdeal_section_marked_product_unit
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (n + 1) ⟶ T),
      (∀ σ, s2_permute Z (n + 1) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z (n + 1))) (a : ComplexPoint Z)
    (S : Finset (Fin (n + 1)))
    (hS : ∀ i, i ∈ S ↔ Point.map (g3_proj Z (n + 1) i) x = a)
    (U : B.left.affineOpens) (hxU : γ.left x.underlying ∈ U.1) :
    ∃ c ∈ (s2c_branchIdeal Z B n γ a).ideal U,
      ∃ u : ((g3_power Z (n + 1)).left.presheaf.stalk x.underlying)ˣ,
        γ.left.stalkMap x.underlying
          (B.left.presheaf.germ U.1 (γ.left x.underlying) hxU c) =
            (∏ i ∈ S, s2e_curvePowerParameter Z (n + 1) x i) * (u : _) := by
  obtain ⟨c, hc, he⟩ := s2e_branchIdeal_marked_product_jet_descent Z B n γ hγ hquot
    x a S hS U hxU (S.card + 1)
  obtain ⟨u, hu⟩ := s2e_branch_section_marked_product_jet_unit Z B n γ hγ a x S
    (fun i hi => (hS i).mp hi) U hxU c hc he
  exact ⟨c, hc, u, hu⟩

end HodgeLean.Foundations.Program
