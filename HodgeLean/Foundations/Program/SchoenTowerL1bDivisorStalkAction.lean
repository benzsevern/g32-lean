import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorStalkComposition
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorOriginalQuotient

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A finite-curve action fixing a point induces actual automorphisms of its stalk. -/
def s2v_l1b_divisor_stalkAction
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (p : X.left) (hfix : ∀ g, (a g).left p = p) :
    G →* (X.left.presheaf.stalk p ≃+* X.left.presheaf.stalk p) := by
  let α (g : G) := s2e_fixed_point_stalkPullback X.left (a g).left p (hfix g)
  have hi (g : G) : IsIso (a g).left := by
    change IsIso ((s2v_l1b_divisor_actionAut X G a ha1 hamul g).asIso.hom.left)
    infer_instance
  have hcomp (g h : G) (v : X.left.presheaf.stalk p) :
      α (g * h) v = α h (α g v) := by
    letI := hi g
    letI := hi h
    have H := s2v_l1b_divisor_fixed_stalk_comp X.left (a h).left (a g).left
      p (hfix h) (hfix g)
      (by rw [Scheme.Hom.comp_apply, hfix h, hfix g]) v
    simpa only [α, hamul, Over.comp_left] using H
  have hone (v : X.left.presheaf.stalk p) : α 1 v = v := by
    simpa only [α, ha1, Over.id_left] using
      s2v_l1b_divisor_fixed_stalk_id X.left p rfl v
  let E (g : G) : X.left.presheaf.stalk p ≃+* X.left.presheaf.stalk p :=
    { α g⁻¹ with
      invFun := α g
      left_inv := fun v => by
        change α g (α g⁻¹ v) = v
        rw [← hcomp, inv_mul_cancel, hone]
      right_inv := fun v => by
        change α g⁻¹ (α g v) = v
        rw [← hcomp, mul_inv_cancel, hone] }
  refine { toFun := E, map_one' := ?_, map_mul' := ?_ }
  · ext v
    exact (show α (1 : G)⁻¹ v = v by rw [inv_one, hone])
  · intro g h
    ext v
    change α (g * h)⁻¹ v = α g⁻¹ (α h⁻¹ v)
    rw [mul_inv_rev, hcomp]

end HodgeLean.Foundations.Program
