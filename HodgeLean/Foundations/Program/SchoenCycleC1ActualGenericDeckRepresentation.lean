import HodgeLean.Foundations.Program.SchoenCycleC1GenericStalkActionHelpers
import HodgeLean.Foundations.Program.SchoenCycleStep1InvariantSections

/-! # Faithful actual generic deck representations over the specified base -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A faithful actual deck action gives a faithful representation on the
specified generic stalk extension, retaining every inverse pullback. -/
theorem s2e_c1_actual_generic_deck_representation
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (hinj : Function.Injective a)
    (q : X ⟶ Y) [IsSeparated q.left] (hinv : ∀ g, a g ≫ q = q)
    (hg : q.left (genericPoint X.left) = genericPoint Y.left) :
    letI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      q.left.stalkMap (genericPoint X.left)).hom
    letI := φ.toAlgebra
    ∃ ρ : G →* (X.left.functionField ≃ₐ[Y.left.functionField] X.left.functionField),
      Function.Injective ρ ∧ ∀ g,
        (ρ g).toRingHom = s2e_step1_fieldPullback X.left (a g⁻¹).left := by
  letI : ∀ g, IsIso (a g) := s2e_step1_action_isIso X G a ha1 hamul
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    q.left.stalkMap (genericPoint X.left)).hom
  letI := φ.toAlgebra
  let ρ : G →* (X.left.functionField ≃ₐ[Y.left.functionField] X.left.functionField) :=
    { toFun := fun g => s2e_c1_deckFunctionFieldEquiv q.left φ
        (s2e_c1_genericStalkMap_square q.left hg) (a g⁻¹).left
        (congrArg Over.Hom.left (hinv g⁻¹))
      map_one' := by
        apply AlgEquiv.ext
        intro z
        change s2e_step1_fieldPullback X.left (a (1 : G)⁻¹).left z = z
        simp only [inv_one, ha1, Over.id_left, s2e_c1_fieldPullback_id, RingHom.id_apply]
      map_mul' := fun g h => by
        apply AlgEquiv.ext
        intro z
        change s2e_step1_fieldPullback X.left (a (g * h)⁻¹).left z =
          s2e_step1_fieldPullback X.left (a g⁻¹).left
            (s2e_step1_fieldPullback X.left (a h⁻¹).left z)
        simp only [mul_inv_rev, hamul, Over.comp_left]
        rw [s2e_c1_fieldPullback_comp]
        rfl }
  refine ⟨ρ, ?_, fun _ => rfl⟩
  intro g h he
  have hf : s2e_step1_fieldPullback X.left (a g⁻¹).left =
      s2e_step1_fieldPullback X.left (a h⁻¹).left :=
    congrArg (fun e : X.left.functionField ≃ₐ[Y.left.functionField] X.left.functionField =>
      e.toRingHom) he
  apply inv_injective
  apply hinj
  apply Over.OverMorphism.ext
  exact s2e_c1_fieldPullback_faithful q.left _ _
    ((congrArg Over.Hom.left (hinv g⁻¹)).trans (congrArg Over.Hom.left (hinv h⁻¹)).symm) hf

end HodgeLean.Foundations.Program
