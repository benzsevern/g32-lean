import HodgeLean.Foundations.Program.SchoenTowerI1aPreDefs
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_action_isIso
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g) (g : G) : IsIso (a g) := by
  refine ⟨⟨a g⁻¹, ?_, ?_⟩⟩
  · rw [← hamul, inv_mul_cancel, ha1]
  · rw [← hamul, mul_inv_cancel, ha1]

lemma s2v_i1ahi_orbit_intersection
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    [IsProjective X.hom] (N : X.left.Opens)
    (A : X.left.Opens) (hA : IsAffineOpen A) (hAN : A ≤ N)
    (x : X.left) (hx : ∀ g, (a g).left x ∈ A) :
    IsAffineOpen (⨅ g, (a g).left ⁻¹ᵁ A) ∧
      (⨅ g, (a g).left ⁻¹ᵁ A) ≤ N ∧
      (∀ h, (⨅ g, (a g).left ⁻¹ᵁ A) ≤
        (a h).left ⁻¹ᵁ (⨅ g, (a g).left ⁻¹ᵁ A)) ∧
      ∀ h, (a h).left x ∈ (⨅ g, (a g).left ⁻¹ᵁ A) := by
  haveI : X.left.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from X.hom]
    infer_instance⟩
  haveI (g : G) : IsIso (a g) := s2v_i1ahi_action_isIso X G a ha1 hamul g
  haveI (g : G) : IsIso (a g).left := inferInstance
  have hm (g h : G) (z : X.left) : (a g).left ((a h).left z) = (a (g * h)).left z := by
    rw [hamul]
    rfl
  refine ⟨IsAffineOpen.iInf (fun g => hA.preimage_of_isIso (a g).left), ?_, ?_, ?_⟩
  · have he : (a (1 : G)).left ⁻¹ᵁ A = A := by rw [ha1]; rfl
    exact (iInf_le_of_le (1 : G) (le_of_eq he)).trans hAN
  · intro h z hz
    change (a h).left z ∈ ⨅ g, (a g).left ⁻¹ᵁ A
    simp only [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    intro g
    change (a g).left ((a h).left z) ∈ A
    rw [hm]
    have hz' : ∀ g, z ∈ (a g).left ⁻¹ᵁ A := by
      simpa only [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter] using hz
    exact hz' (g * h)
  · intro h
    simp only [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    intro g
    change (a g).left ((a h).left x) ∈ A
    rw [hm]
    exact hx (g * h)

end HodgeLean.Foundations.Program
