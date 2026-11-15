import HodgeLean.Foundations.Program.SchoenCycleC1SymmetricStalkUnitDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A signed equation at one actual symmetric tuple gives an exact base
chart unit factorization on a common affine neighbourhood. -/
theorem s2e_c1_symmetric_stalk_signed_factor_descent
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] (N : ℕ)
    (γ : g3_power Z N ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z N ⟶ T),
      (∀ σ, s2_permute Z N σ ≫ v = v) → ∃! w : B ⟶ T, γ ≫ w = v)
    (x : ComplexPoint (g3_power Z N)) (U : B.left.Opens) (hx : γ.left x.underlying ∈ U)
    {ι : Type*} [Fintype ι] (c : ι → B.left.functionField) (hc : ∀ j, c j ≠ 0)
    (n : ι → ℤ) (t : B.left.functionField) :
    letI : Surjective γ.left := s2e_c11_surjective_of_point_surjective (g3_power Z N) B γ hsurj
    let hg := s2e_c1_dominant_generic_point γ.left
    let φ := (eqToHom (congrArg B.left.presheaf.stalk hg.symm) ≫
      γ.left.stalkMap (genericPoint (g3_power Z N).left)).hom
    (∃ u : ((g3_power Z N).left.presheaf.stalk x.underlying)ˣ,
      φ t = algebraMap ((g3_power Z N).left.presheaf.stalk x.underlying)
        (g3_power Z N).left.functionField (u : _) * ∏ j, (φ (c j)) ^ n j) →
    ∃ (V : B.left.affineOpens) (hxV : γ.left x.underlying ∈ V.1), V.1 ≤ U ∧
      letI : Nonempty V.1 := ⟨⟨γ.left x.underlying, hxV⟩⟩
      ∃ v : Γ(B.left, V.1)ˣ, t = B.left.germToFunctionField V.1 (v : Γ(B.left, V.1)) *
        ∏ j, c j ^ n j := by
  letI : Surjective γ.left := s2e_c11_surjective_of_point_surjective (g3_power Z N) B γ hsurj
  dsimp only
  let hg := s2e_c1_dominant_generic_point γ.left
  let φ := (eqToHom (congrArg B.left.presheaf.stalk hg.symm) ≫
    γ.left.stalkMap (genericPoint (g3_power Z N).left)).hom
  rintro ⟨u, hu⟩
  let d := ∏ j, c j ^ n j
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => zpow_ne_zero _ (hc j))
  have hdφ : φ d ≠ 0 := fun he => hd (φ.injective (he.trans (map_zero φ).symm))
  have hmap : φ d = ∏ j, (φ (c j)) ^ n j := by simp only [d, map_prod, map_zpow₀]
  have hratio : φ (t / d) =
      algebraMap ((g3_power Z N).left.presheaf.stalk x.underlying)
        (g3_power Z N).left.functionField (u : _) := by
    rw [map_div₀, hu, ← hmap]
    exact mul_div_cancel_right₀ _ hdφ
  have hne : t / d ≠ 0 := by
    intro he
    have hn := (Units.map (algebraMap ((g3_power Z N).left.presheaf.stalk x.underlying)
      (g3_power Z N).left.functionField).toMonoidHom u).ne_zero
    apply hn
    change algebraMap ((g3_power Z N).left.presheaf.stalk x.underlying)
      (g3_power Z N).left.functionField (u : _) = 0
    rw [← hratio, he, map_zero]
  obtain ⟨V, hxV, hVU, v, hv⟩ := s2e_c1_symmetric_stalk_unit_descent Z B N γ hsurj hγ hquot
    x U hx (t / d) hne ⟨u, hratio.symm⟩
  letI : Nonempty V.1 := ⟨⟨γ.left x.underlying, hxV⟩⟩
  refine ⟨V, hxV, hVU, v, ?_⟩
  change t = B.left.germToFunctionField V.1 (v : Γ(B.left, V.1)) * d
  rw [hv]
  exact (div_mul_cancel₀ t hd).symm

end HodgeLean.Foundations.Program
