import HodgeLean.Foundations.Program.SchoenCycleC1NormalInvariantDescent
import HodgeLean.Foundations.Program.SchoenCycleC1SectionFieldTowerHelpers
import HodgeLean.Foundations.Program.SchoenCycleQuotientBaseAction
import HodgeLean.Foundations.Program.SchoenCycleStep1InvariantSections

/-! # Actual affine section descent from measured generic deck invariants -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- On a normal affine base chart, measured faithful generic deck pullbacks
identify the actual invariant regular sections with the actual base sections. -/
theorem s2e_c1_measured_affine_section_descent
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (q : X ⟶ Y) [IsFinite q.left] (hinv : ∀ g, a g ≫ q = q)
    (hg : q.left (genericPoint X.left) = genericPoint Y.left)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    [Nonempty U] [Nonempty (q.left ⁻¹ᵁ U)] [IsIntegrallyClosed Γ(Y.left, U)] :
    letI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      q.left.stalkMap (genericPoint X.left)).hom
    letI := φ.toAlgebra
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    ∀ [Module.Finite Y.left.functionField X.left.functionField]
      (ρ : G →* (X.left.functionField ≃ₐ[Y.left.functionField] X.left.functionField)),
      Function.Injective ρ → Module.finrank Y.left.functionField X.left.functionField = Nat.card G →
      (∀ g, (ρ g).toRingHom = s2e_step1_fieldPullback X.left (a g⁻¹).left) →
      ∀ b : Γ(X.left, q.left ⁻¹ᵁ U),
        (∀ g : G, g • b = b) ↔ ∃ r : Γ(Y.left, U), (q.left.app U).hom r = b := by
  letI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    q.left.stalkMap (genericPoint X.left)).hom
  letI := φ.toAlgebra
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  dsimp only
  intro hfinite ρ hρ hdeg hρval b
  letI := hfinite
  let R := Γ(Y.left, U)
  let S := Γ(X.left, q.left ⁻¹ᵁ U)
  letI : Algebra R S := (q.left.app U).hom.toAlgebra
  letI : Algebra R X.left.functionField :=
    ((X.left.germToFunctionField (q.left ⁻¹ᵁ U)).hom.comp (q.left.app U).hom).toAlgebra
  letI : IsScalarTower R S X.left.functionField := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R Y.left.functionField X.left.functionField :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (s2e_c1_genericStalkMap_comp_germ q.left hg U)).symm
  letI : IsFractionRing R Y.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y.left U hU
  letI : IsFractionRing S X.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen X.left _ (hU.preimage q.left)
  letI : Module.Finite R S := q.left.finite_app U hU
  letI := s2e_quotient_sectionAction_base_smulComm X Y G a ha1 hamul q hinv U
  let τ := MulSemiringAction.toAlgAut G R S
  haveI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
  have hc (g : G) (s : S) : ρ g (algebraMap S X.left.functionField s) =
      algebraMap S X.left.functionField (τ g s) := by
    change (ρ g).toRingHom ((X.left.germToFunctionField _).hom s) = _
    rw [hρval]
    exact congrArg (fun f : Γ(X.left, q.left ⁻¹ᵁ U) ⟶ CommRingCat.of X.left.functionField => f.hom s)
      (s2e_step1_fieldPullback_germ X.left (a g⁻¹).left _ _
        (s2e_step1_action_preimage X Y q (a g⁻¹) (hinv g⁻¹) U))
  exact s2e_c1_normal_regular_invariant_descent τ ρ hρ hdeg hc b

end HodgeLean.Foundations.Program
