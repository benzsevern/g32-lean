import HodgeLean.Foundations.Program.SchoenCycleBranchIdealJetDescent
import HodgeLean.Foundations.Program.SchoenCycleQuotientPrincipalStalks
import HodgeLean.Foundations.Program.SchoenCycleAffineIdealShrinking

/-! # Actual mixed marked insertion ideals are principal -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- The actual mixed insertion-image stalk ideal has a generator whose pullback is the marked product times a unit.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.2 and II.5. -/
theorem s2e_mixed_branch_stalk_principal
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
      Ideal.map (B.left.presheaf.germ U.1 (γ.left x.underlying) hxU).hom
        ((s2c_branchIdeal Z B n γ a).ideal U) =
          Ideal.span {B.left.presheaf.germ U.1 (γ.left x.underlying) hxU c} ∧
      ∃ u : ((g3_power Z (n + 1)).left.presheaf.stalk x.underlying)ˣ,
        γ.left.stalkMap x.underlying
          (B.left.presheaf.germ U.1 (γ.left x.underlying) hxU c) =
            (∏ i ∈ S, s2e_curvePowerParameter Z (n + 1) x i) * (u : _) := by
  obtain ⟨c, hc, u, hu⟩ := s2e_branchIdeal_section_marked_product_unit Z B n γ hγ hquot
    x a S hS U hxU
  let X := g3_power Z (n + 1)
  let W := γ.left ⁻¹ᵁ U.1
  let ψ := (X.left.presheaf.germ W x.underlying hxU).hom
  have hr : γ.left.stalkMap x.underlying
      (B.left.presheaf.germ U.1 (γ.left x.underlying) hxU c) ≠ 0 := by
    rw [hu]
    exact mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun i _ => s2e_curvePowerParameter_ne_zero Z (n + 1) x i))
      u.ne_zero
  have hreg : Function.Injective (fun z : Γ(X.left, W) => (γ.left.app U.1).hom c * z) := by
    intro v w hvw
    apply germ_injective_of_isIntegral X.left x.underlying hxU
    apply mul_left_cancel₀ (show ψ ((γ.left.app U.1).hom c) ≠ 0 by
      rwa [← γ.left.germ_stalkMap_apply U.1 x.underlying hxU])
    simpa only [map_mul] using congrArg ψ hvw
  letI : IsClosedImmersion (x.left ≫ X.hom) := by
    rw [Over.w x]
    change IsClosedImmersion (𝟙 (Spec ↧ℂ))
    infer_instance
  letI : IsClosedImmersion x.left := IsClosedImmersion.of_comp x.left X.hom
  have hclosed : IsClosed ({x.underlying} : Set X.left) := by
    change IsClosed {x.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using x.left.isClosedMap {IsLocalRing.closedPoint ℂ}
      (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  refine ⟨c, hc, ?_, u, hu⟩
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro s hs
    apply Ideal.mem_span_singleton.mpr
    apply s2e_quotient_principal_stalk_divisibility X B (Equiv.Perm (Fin (n + 1)))
      (s2_permute Z (n + 1)) (s2e_step1_permute_one Z (n + 1))
      (s2e_step1_permute_mul Z (n + 1)) γ hγ hquot U
      (s2e_powerPointStabilizer Z (n + 1) x) x hxU hclosed (fun _ => Iff.rfl) c s hreg
    rw [hu]
    apply u.isUnit.mul_right_dvd.mpr
    exact s2e_branch_section_marked_product_dvd Z B n γ hγ a x S
      (fun i hi => (hS i).mp hi) U hxU s hs
  · apply Ideal.span_le.mpr
    intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact Ideal.mem_map_of_mem _ hc

/-- The actual mixed insertion-image ideal has an affine generator retaining its marked-product pullback and local unit.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.2 and II.5. -/
theorem s2e_mixed_branch_affine_generator
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    [Smooth B.hom]
    (n : ℕ) (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (n + 1) ⟶ T),
      (∀ σ, s2_permute Z (n + 1) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z (n + 1))) (a : ComplexPoint Z)
    (S : Finset (Fin (n + 1)))
    (hS : ∀ i, i ∈ S ↔ Point.map (g3_proj Z (n + 1) i) x = a) :
    ∃ (U : B.left.affineOpens) (hxU : γ.left x.underlying ∈ U.1)
      (c : Γ(B.left, U.1)), (s2c_branchIdeal Z B n γ a).ideal U = Ideal.span {c} ∧
      ∃ u : ((g3_power Z (n + 1)).left.presheaf.stalk x.underlying)ˣ,
        γ.left.stalkMap x.underlying
          (B.left.presheaf.germ U.1 (γ.left x.underlying) hxU c) =
            (∏ i ∈ S, s2e_curvePowerParameter Z (n + 1) x i) * (u : _) := by
  letI : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  obtain ⟨U, hU, hxU, _hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show γ.left x.underlying ∈ (⊤ : B.left.Opens) from trivial)
  obtain ⟨c, hc, he, u, hu⟩ := s2e_mixed_branch_stalk_principal Z B n γ hγ hquot
    x a S hS ⟨U, hU⟩ hxU
  obtain ⟨V, hVU, hxV, t, ht, htr⟩ := s2e_affine_generator_of_stalk_generator
    B.left (s2c_branchIdeal Z B n γ a) ⟨U, hU⟩ (γ.left x.underlying) hxU
    (B.left.presheaf.germ U (γ.left x.underlying) hxU c) he
  exact ⟨V, hxV, t, ht, u, by rw [htr]; exact hu⟩

end HodgeLean.Foundations.Program
