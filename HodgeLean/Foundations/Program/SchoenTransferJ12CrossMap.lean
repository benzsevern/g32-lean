import HodgeLean.Foundations.Program.SchoenTransferPairing

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- The actual Künneth map in a single specified bidegree. -/
def s4_selected_cross_map
    (A : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ))
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (p q m : ℕ) (h : p + q = m) :
    HQ A p ⊗[ℚ] HQ B q →ₗ[ℚ] HQ (A ⊗ B) m :=
  TensorProduct.lift (((cupProductOf (A ⊗ B)).cup h).compl₁₂
    (homPullback (fst A B) p) (homPullback (snd A B) q))

/-- Evaluation of the single-bidegree Künneth map on a pure tensor. -/
theorem s4_selected_cross_map_tmul
    (A : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ))
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (p q m : ℕ) (h : p + q = m) (a : HQ A p) (b : HQ B q) :
    s4_selected_cross_map A B p q m h (a ⊗ₜ[ℚ] b) =
      (cupProductOf (A ⊗ B)).cup h
        (homPullback (fst A B) p a) (homPullback (snd A B) q b) := rfl

/-- Products of Künneth bidegrees add the two factor degrees separately. -/
theorem s4_selected_cross_map_cup_mem
    (A : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ))
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (u v s t m n p q l : ℕ)
    (huv : u + v = m) (hst : s + t = n)
    (hp : u + s = p) (hq : v + t = q) (hl : m + n = l)
    (x : HQ (A ⊗ B) m) (y : HQ (A ⊗ B) n)
    (hx : x ∈ LinearMap.range (s4_selected_cross_map A B u v m huv))
    (hy : y ∈ LinearMap.range (s4_selected_cross_map A B s t n hst)) :
    (cupProductOf (A ⊗ B)).cup hl x y ∈
      LinearMap.range (s4_selected_cross_map A B p q l (by omega)) := by
  obtain ⟨ξ, rfl⟩ := LinearMap.mem_range.mp hx
  obtain ⟨η, rfl⟩ := LinearMap.mem_range.mp hy
  clear hx hy
  induction ξ using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
  | tmul a b =>
      induction η using TensorProduct.induction_on with
      | zero =>
          simp only [map_zero]
          exact Submodule.zero_mem _
      | tmul c e =>
          rw [s4_selected_cross_map_tmul, s4_selected_cross_map_tmul,
            s4_cup_middle_exchange (A ⊗ B) (cupProductOf (A ⊗ B))
              u v s t m n p q l huv hst hp hq hl,
            ← spec_homPullback_cup (fst A B) hp,
            ← spec_homPullback_cup (snd A B) hq]
          apply Submodule.smul_mem
          exact LinearMap.mem_range.mpr
            ⟨((cupProductOf A).cup hp a c) ⊗ₜ[ℚ] ((cupProductOf B).cup hq b e), rfl⟩
      | add ξ η hξ hη =>
          simpa only [map_add] using Submodule.add_mem _ hξ hη
  | add ξ η hξ hη =>
      simpa only [map_add, LinearMap.add_apply] using Submodule.add_mem _ hξ hη


#print axioms s4_selected_cross_map_cup_mem
end HodgeLean.Foundations.Program
