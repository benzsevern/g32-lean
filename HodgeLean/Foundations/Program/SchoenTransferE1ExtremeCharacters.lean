import HodgeLean.Foundations.Program.SchoenTransferE1CurveRepresentation
import HodgeLean.Foundations.Program.SchoenTransferE1TopAction

/-! Character spaces in the extreme curve degrees for the supplied action. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

/-- A group action given by actual scheme maps consists of isomorphisms.
Source: the group inverse law and functoriality of an action. -/
theorem s4_e1_curve_action_isIso
    {G : Type*} [Group G] (Y : Over (Spec ↧ℂ)) (a : G → (Y ⟶ Y))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v) (g : G) :
    IsIso (a g) := by
  refine ⟨⟨a g⁻¹, ?_, ?_⟩⟩
  · rw [← hamul, mul_inv_cancel, ha1]
  · rw [← hamul, inv_mul_cancel, ha1]

/-- The actual supplied action is the identity in degrees zero and two on a curve.
Source: Schoen (1988), Lemma 1.1, p. 5; preservation of complex orientation. -/
theorem s4_e1_curve_action_extreme_identity
    {G : Type*} [Group G]
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (a : G → (Y ⟶ Y))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v) (g : G) :
    homPullback (a g) 0 = LinearMap.id ∧ homPullback (a g) 2 = LinearMap.id := by
  letI := s4_e1_curve_action_isIso Y a ha1 hamul g
  refine ⟨s4_e1_degree_zero_action Y (a g), ?_⟩
  letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdim]; infer_instance
  exact s4_e1_top_rational_action Y 1 (asIso (a g))

/-- The identity operator has no nontrivial character space.
Source: Schoen (1988), Lemma 1.1, p. 5; scalar eigenspaces. -/
theorem s4_e1_identity_eigenspace
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ζ : ℂ) (hζ : ζ ≠ 1) :
    Module.End.eigenspace (LinearMap.id : Module.End ℂ V) ζ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have he : x = ζ • x := Module.End.mem_eigenspace_iff.mp hx
  have hz : (1 - ζ) • x = 0 := by rw [sub_smul, one_smul, ← he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hζ.symm)

/-- Every nontrivial complex character space vanishes in the two extreme curve degrees.
Source: Schoen (1988), Lemma 1.1, p. 5; the actual supplied curve action. -/
theorem s4_e1_curve_extreme_character_spaces
    {G : Type*} [Group G]
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (a : G → (Y ⟶ Y))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (g : G) (ζ : ℂ) (hζ : ζ ≠ 1) :
    Module.End.eigenspace ((homPullback (a g) 0).baseChange ℂ) ζ = ⊥ ∧
      Module.End.eigenspace ((homPullback (a g) 2).baseChange ℂ) ζ = ⊥ := by
  have he := s4_e1_curve_action_extreme_identity Y hdim a ha1 hamul g
  simp only [he.1, he.2, LinearMap.baseChange_id]
  exact ⟨s4_e1_identity_eigenspace ζ hζ, s4_e1_identity_eigenspace ζ hζ⟩

#print axioms s4_e1_curve_action_isIso
#print axioms s4_e1_curve_action_extreme_identity
#print axioms s4_e1_identity_eigenspace
#print axioms s4_e1_curve_extreme_character_spaces
end HodgeLean.Foundations.Program
