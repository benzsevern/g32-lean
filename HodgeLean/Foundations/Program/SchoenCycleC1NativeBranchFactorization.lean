import HodgeLean.Foundations.Program.SchoenCycleC1FiniteBranchGenerators
import HodgeLean.Foundations.Program.SchoenCycleC1SignedProductGrouping
import HodgeLean.Foundations.Program.SchoenCycleC1SymmetricStalkFactorDescent
import HodgeLean.Foundations.Program.SchoenCycleC1GenericLocalFieldSquare
import HodgeLean.Foundations.Program.SchoenCycleC1RationalRestriction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The original native tuple equation produces an affine factorization by
actual insertion branch generators, retaining repeated coordinates and signed orders. -/
theorem s2e_c1_native_branch_factorization
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] (N : ℕ)
    (γ : g3_power Z (N + 1) ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z (N + 1) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (N + 1) ⟶ T),
      (∀ σ, s2_permute Z (N + 1) σ ≫ v = v) → ∃! w : B ⟶ T, γ ≫ w = v)
    (x : ComplexPoint (g3_power Z (N + 1)))
    {J : Type*} [Fintype J] [DecidableEq J]
    (a : J → ComplexPoint Z) (ha : Function.Injective a) (g : Fin (N + 1) → J)
    (hgcoord : ∀ i, a (g i) = Point.map (g3_proj Z (N + 1) i) x)
    (n : J → ℤ) (t : B.left.functionField)
    (U : B.left.Opens) (hxU : γ.left x.underlying ∈ U) :
    letI : Surjective γ.left := s2e_c11_surjective_of_point_surjective (g3_power Z (N + 1)) B γ hsurj
    let hg := s2e_c1_dominant_generic_point γ.left
    let φ := (eqToHom (congrArg B.left.presheaf.stalk hg.symm) ≫
      γ.left.stalkMap (genericPoint (g3_power Z (N + 1)).left)).hom
    (∃ u : ((g3_power Z (N + 1)).left.presheaf.stalk x.underlying)ˣ,
      φ t = algebraMap ((g3_power Z (N + 1)).left.presheaf.stalk x.underlying)
        (g3_power Z (N + 1)).left.functionField (u : _) *
        ∏ i, (algebraMap ((g3_power Z (N + 1)).left.presheaf.stalk x.underlying)
          (g3_power Z (N + 1)).left.functionField (s2e_curvePowerParameter Z (N + 1) x i)) ^ n (g i)) →
    ∃ (V : B.left.affineOpens) (hxV : γ.left x.underlying ∈ V.1), V.1 ≤ U ∧
      letI : Nonempty V.1 := ⟨⟨γ.left x.underlying, hxV⟩⟩
      ∃ (c : J → Γ(B.left, V.1)) (v : Γ(B.left, V.1)ˣ),
        (∀ j, (s2c_branchIdeal Z B N γ (a j)).ideal V = Ideal.span {c j} ∧ c j ≠ 0) ∧
        t = B.left.germToFunctionField V.1 (v : Γ(B.left, V.1)) *
          ∏ j, (B.left.germToFunctionField V.1 (c j)) ^ n j := by
  classical
  letI : Surjective γ.left := s2e_c11_surjective_of_point_surjective (g3_power Z (N + 1)) B γ hsurj
  dsimp only
  let hg := s2e_c1_dominant_generic_point γ.left
  let φ := (eqToHom (congrArg B.left.presheaf.stalk hg.symm) ≫
    γ.left.stalkMap (genericPoint (g3_power Z (N + 1)).left)).hom
  rintro ⟨u, hu⟩
  let S (j : J) := Finset.univ.filter (fun i => g i = j)
  have hS (j : J) (i : Fin (N + 1)) : i ∈ S j ↔ Point.map (g3_proj Z (N + 1) i) x = a j := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun he => (hgcoord i).symm.trans (congrArg a he), fun he => ha ((hgcoord i).trans he)⟩
  obtain ⟨W, hxW, hWU, c, hc⟩ := s2e_c1_finite_branch_generators Z B N γ hγ hquot x a S hS U hxU
  letI : Nonempty W.1 := ⟨⟨γ.left x.underlying, hxW⟩⟩
  choose v hv using fun j => (hc j).2.2
  let R := (g3_power Z (N + 1)).left.presheaf.stalk x.underlying
  let K := (g3_power Z (N + 1)).left.functionField
  let b (j : J) : R := γ.left.stalkMap x.underlying
    (B.left.presheaf.germ W.1 (γ.left x.underlying) hxW (c j))
  let cK (j : J) := B.left.germToFunctionField W.1 (c j)
  have hcK (j : J) : cK j ≠ 0 := by
    intro he
    exact (hc j).2.1 (B.left.germToFunctionField_injective W.1 (he.trans (map_zero _).symm))
  have hmap (j : J) : φ (cK j) = algebraMap R K (b j) := by
    change φ (B.left.germToFunctionField W.1 (c j)) = _
    rw [← B.left.algebraMap_germ_eq_germToFunctionField hxW (c j)]
    exact s2e_c1_generic_stalk_map_local_square γ.left hg x.underlying _
  obtain ⟨w, hw⟩ := s2e_c1_signed_product_grouping (algebraMap R K) g
    (s2e_curvePowerParameter Z (N + 1) x) b v hv n u
  have hfactor : φ t = algebraMap R K (w : R) * ∏ j, (φ (cK j)) ^ n j := by
    rw [hu, hw]
    simp_rw [hmap]
  obtain ⟨V, hxV, hVW, wV, hwV⟩ := s2e_c1_symmetric_stalk_signed_factor_descent
    Z B (N + 1) γ hsurj hγ hquot x W.1 hxW cK hcK n t ⟨w, hfactor⟩
  letI : Nonempty V.1 := ⟨⟨γ.left x.underlying, hxV⟩⟩
  let c' (j : J) := (B.left.presheaf.map (homOfLE (X := B.left.Opens) hVW).op).hom (c j)
  have hr (j : J) : B.left.germToFunctionField V.1 (c' j) = cK j :=
    s2e_c1_rational_section_restriction B.left W.1 V.1 hVW (c j)
  refine ⟨V, hxV, hVW.trans hWU, c', wV, ?_, ?_⟩
  · intro j
    constructor
    · rw [← (s2c_branchIdeal Z B N γ (a j)).map_ideal hVW, (hc j).1,
        Ideal.map_span, Set.image_singleton]
      rfl
    · intro he
      apply hcK j
      rw [← hr, he, map_zero]
  · simp_rw [hr]
    exact hwV

end HodgeLean.Foundations.Program
