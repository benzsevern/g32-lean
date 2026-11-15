import HodgeLean.Foundations.Program.SchoenCycleC1MeasuredSectionDescent
import Mathlib.RingTheory.Invariant.Basic

/-! # The measured invariant extension on actual affine sections -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Measured generic pullbacks supply the invariant-extension interface for
the actual section rings over a normal affine base chart. -/
theorem s2e_c1_measured_section_invariant_extension
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
    letI : Algebra Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) := (q.left.app U).hom.toAlgebra
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    ∀ [Module.Finite Y.left.functionField X.left.functionField]
      (ρ : G →* (X.left.functionField ≃ₐ[Y.left.functionField] X.left.functionField)),
      Function.Injective ρ → Module.finrank Y.left.functionField X.left.functionField = Nat.card G →
      (∀ g, (ρ g).toRingHom = s2e_step1_fieldPullback X.left (a g⁻¹).left) →
      Algebra.IsInvariant Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) G := by
  letI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    q.left.stalkMap (genericPoint X.left)).hom
  letI := φ.toAlgebra
  letI : Algebra Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) := (q.left.app U).hom.toAlgebra
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  dsimp only
  intro hfinite ρ hρ hdeg hρval
  letI := hfinite
  exact ⟨fun b hb => (s2e_c1_measured_affine_section_descent
    X Y G a ha1 hamul q hinv hg U hU ρ hρ hdeg hρval b).mp hb⟩

end HodgeLean.Foundations.Program
