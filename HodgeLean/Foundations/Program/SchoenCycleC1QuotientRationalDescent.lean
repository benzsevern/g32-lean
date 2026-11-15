import HodgeLean.Foundations.Program.SchoenCycleC1BaseDenominator
import HodgeLean.Foundations.Program.SchoenCycleC1DominantGenericPoint
import HodgeLean.Foundations.Program.SchoenCycleC1SectionFieldTowerHelpers
import HodgeLean.Foundations.Program.SchoenCycleStep1InvariantSections

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Every actual invariant rational function descends through the retained
finite categorical quotient, retaining its exact generic stalk embedding.
The denominator is constructed in the original base section ring. -/
theorem s2e_c1_quotient_rational_descent
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (I : Type) (a : I → (X ⟶ X)) [∀ i, IsIso (a i)]
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ i, a i ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ i, a i ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (F : X.left.functionField)
    (hF : ∀ i, s2e_step1_fieldPullback X.left (a i).left F = F) :
    let hg := s2e_c1_dominant_generic_point q.left
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      q.left.stalkMap (genericPoint X.left)).hom
    ∃ d : Y.left.functionField, φ d = F := by
  dsimp only
  let hg := s2e_c1_dominant_generic_point q.left
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    q.left.stalkMap (genericPoint X.left)).hom
  obtain ⟨U, hU, hpU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y.left) (x := genericPoint Y.left) (U := ⊤) (by trivial)
  letI : Nonempty U := ⟨⟨genericPoint Y.left, hpU⟩⟩
  let W := q.left ⁻¹ᵁ U
  letI : Nonempty W := ⟨⟨genericPoint X.left, by change q.left (genericPoint X.left) ∈ U; rwa [hg]⟩⟩
  let R := Γ(Y.left, U)
  let S := Γ(X.left, W)
  let L := X.left.functionField
  letI : Algebra R S := (q.left.app U).hom.toAlgebra
  letI : Algebra R L := ((X.left.germToFunctionField W).hom.comp (q.left.app U).hom).toAlgebra
  letI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite R S := q.left.finite_app U hU
  letI : IsSchemeTheoreticallyDominant q.left := .of_isDominant q.left
  letI : FaithfulSMul R S :=
    (faithfulSMul_iff_algebraMap_injective R S).mpr (q.left.app_injective U)
  letI : IsFractionRing S L := functionField_isFractionRing_of_isAffineOpen X.left W (hU.preimage q.left)
  obtain ⟨r, hr, b, hb⟩ := s2e_c1_base_denominator (R := R) (S := S) F
  have hUV (i : I) : W ≤ (a i).left ⁻¹ᵁ W := by
    change q.left ⁻¹ᵁ U ≤ ((a i).left ≫ q.left) ⁻¹ᵁ U
    have hi : (a i).left ≫ q.left = q.left := congrArg Over.Hom.left (hinv i)
    rw [hi]
  have hbF (i : I) : s2e_step1_fieldPullback X.left (a i).left
      (X.left.germToFunctionField W b) = X.left.germToFunctionField W b := by
    change s2e_step1_fieldPullback X.left (a i).left (algebraMap S L b) = algebraMap S L b
    rw [← hb, map_mul]
    have hbase : s2e_step1_fieldPullback X.left (a i).left (algebraMap R L r) = algebraMap R L r :=
      s2e_step1_fieldPullback_base X.left Y.left (a i).left q.left
        (congrArg Over.Hom.left (hinv i)) U r
    rw [hbase, hF i]
  have hbsection (i : I) : ((a i).left.appLE W W (hUV i)).hom b = b := by
    apply X.left.germToFunctionField_injective W
    have he := congrArg (fun k : Γ(X.left, W) ⟶ X.left.functionField => k.hom b)
      (s2e_step1_fieldPullback_germ X.left (a i).left W W (hUV i))
    exact he.symm.trans (hbF i)
  obtain ⟨c, hc, _⟩ := s2e_step1_invariant_sections X Y I a q hinv hquot U hU b hbsection
  have hφ (s : R) : φ (Y.left.germToFunctionField U s) =
      X.left.germToFunctionField W ((q.left.app U).hom s) :=
    congrArg (fun k : Γ(Y.left, U) ⟶ X.left.functionField => k.hom s)
      (s2e_c1_genericStalkMap_comp_germ q.left hg U)
  have hrK : Y.left.germToFunctionField U r ≠ 0 :=
    fun h => hr (Y.left.germToFunctionField_injective U (h.trans (map_zero _).symm))
  have hrL : algebraMap R L r ≠ 0 := by
    change X.left.germToFunctionField W ((q.left.app U).hom r) ≠ 0
    rw [← hφ r]
    exact fun h => hrK (φ.injective (h.trans (map_zero _).symm))
  refine ⟨Y.left.germToFunctionField U c / Y.left.germToFunctionField U r, ?_⟩
  rw [map_div₀, hφ, hφ, hc]
  change algebraMap S L b / algebraMap R L r = F
  rw [← hb, mul_comm]
  exact mul_div_cancel_right₀ _ hrL

end HodgeLean.Foundations.Program
