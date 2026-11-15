import HodgeLean.Foundations.Program.SchoenCycleMixedBranchPrincipality

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A finite family of actual insertion branches has simultaneous affine
generators retaining all marked-product stalk equations on one neighbourhood. -/
theorem s2e_c1_finite_branch_generators
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] (n : ℕ)
    (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (n + 1) ⟶ T),
      (∀ σ, s2_permute Z (n + 1) σ ≫ v = v) → ∃! w : B ⟶ T, γ ≫ w = v)
    (x : ComplexPoint (g3_power Z (n + 1)))
    {J : Type*} [Fintype J] (a : J → ComplexPoint Z) (S : J → Finset (Fin (n + 1)))
    (hS : ∀ j i, i ∈ S j ↔ Point.map (g3_proj Z (n + 1) i) x = a j)
    (U : B.left.Opens) (hxU : γ.left x.underlying ∈ U) :
    ∃ (V : B.left.affineOpens) (hxV : γ.left x.underlying ∈ V.1), V.1 ≤ U ∧
      ∃ c : J → Γ(B.left, V.1), ∀ j,
        (s2c_branchIdeal Z B n γ (a j)).ideal V = Ideal.span {c j} ∧ c j ≠ 0 ∧
        ∃ u : ((g3_power Z (n + 1)).left.presheaf.stalk x.underlying)ˣ,
          γ.left.stalkMap x.underlying
            (B.left.presheaf.germ V.1 (γ.left x.underlying) hxV (c j)) =
              (∏ i ∈ S j, s2e_curvePowerParameter Z (n + 1) x i) * (u : _) := by
  classical
  have he (j : J) := s2e_mixed_branch_affine_generator Z B n γ hγ hquot x (a j) (S j) (hS j)
  choose W hxW c hc u hu using he
  have hxO : γ.left x.underlying ∈ U ⊓ ⨅ j, (W j).1 := by
    constructor
    · exact hxU
    · simpa only [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter] using hxW
  obtain ⟨V, hV, hxV, hVO⟩ := exists_isAffineOpen_mem_and_subset hxO
  have hVO' : V ≤ U ⊓ ⨅ j, (W j).1 := hVO
  let Vb : B.left.affineOpens := ⟨V, hV⟩
  have hVW (j : J) : Vb ≤ W j := hVO'.trans (inf_le_right.trans (iInf_le _ j))
  let c' (j : J) := (B.left.presheaf.map (homOfLE (X := B.left.Opens) (hVW j)).op).hom (c j)
  have hgerm (j : J) : B.left.presheaf.germ V (γ.left x.underlying) hxV (c' j) =
      B.left.presheaf.germ (W j).1 (γ.left x.underlying) (hxW j) (c j) := by
    change (B.left.presheaf.map (homOfLE (X := B.left.Opens) (hVW j)).op ≫
      B.left.presheaf.germ V (γ.left x.underlying) hxV).hom (c j) = _
    rw [B.left.presheaf.germ_res]
  refine ⟨Vb, hxV, hVO.trans inf_le_left, c', ?_⟩
  intro j
  have hprod : γ.left.stalkMap x.underlying
      (B.left.presheaf.germ V (γ.left x.underlying) hxV (c' j)) =
        (∏ i ∈ S j, s2e_curvePowerParameter Z (n + 1) x i) * (u j : _) := by
    rw [hgerm]
    exact hu j
  refine ⟨?_, ?_, u j, hprod⟩
  · rw [← (s2c_branchIdeal Z B n γ (a j)).map_ideal (hVW j), hc j,
      Ideal.map_span, Set.image_singleton]
    rfl
  · intro hz
    have hn : (∏ i ∈ S j, s2e_curvePowerParameter Z (n + 1) x i) * (u j : _) ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr
      (fun i _ => s2e_curvePowerParameter_ne_zero Z (n + 1) x i)) (u j).ne_zero
    apply hn
    rw [← hprod, hz, map_zero, map_zero]

end HodgeLean.Foundations.Program
