import HodgeLean.Foundations.Program.G32ContractionDefs
import HodgeLean.Foundations.Program.G32ContractionWedge
import HodgeLean.Foundations.Program.G32ContractionMaps
import HodgeLean.Foundations.Program.CycleFoundations

/-! # Bodies of the first stage of the G32 contraction

One auxiliary body per statement of `G32Contraction.lean`. HC no distance; AV milestone no
distance.
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

set_option maxRecDepth 4000 in
theorem g32c_contraction_tensor_aux (Y B : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (c p q e : ℕ) (h : 2 * c + 2 * p = 2 * q + 2 * d) (hc : 2 * q + 2 * e = 2 * c)
    (hd : 2 * e + 2 * p = 2 * d) (a : HQ Y (2 * q)) (b : HQ B (2 * e)) (x : HQ B (2 * p)) :
    cfd_corrAction Y B d I c p q h
      ((cupProductOf (Y ⊗ B)).cup hc (homPullback (fst Y B) (2 * q) a)
        (homPullback (snd Y B) (2 * e) b)) x =
      I ((cupProductOf B).cup hd b x) • a := by
  have h1 := (cupProductOf (Y ⊗ B)).assoc hc hd h rfl (homPullback (fst Y B) (2 * q) a)
    (homPullback (snd Y B) (2 * e) b) (homPullback (snd Y B) (2 * p) x)
  have h2 := congrArg ((cupProductOf (Y ⊗ B)).cup (rfl : 2 * q + 2 * d = 2 * q + 2 * d)
    (homPullback (fst Y B) (2 * q) a)) (spec_homPullback_cup (snd Y B) hd b x).symm
  exact (congrArg (cfd_projection Y B d I (2 * q)) (h1.trans h2)).trans
    (cfd_projection_cross Y B d hB I (2 * q) a ((cupProductOf B).cup hd b x))

theorem g32c_coLine_mul_ne_zero_aux {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {m h : ℕ} [NeZero m] (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m))
    (t : cyc_Field m →ₐ[ℚ] ℂ) (n : ℕ) (Z : ⋀[ℂ]^n (ℂ ⊗[ℚ] V)) (hZ : Z ∈ g32c_coLine e t n)
    (hZ0 : Z ≠ 0) (w : ⋀[ℚ]^h V) (hw : w ∈ cyc_wedges e) (hw0 : w ≠ 0) :
    (Z : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] V)) *
      (HodgeBlocks.complexifyWedge h w : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] V)) ≠ 0 :=
  g32c_coLine_mul_ne_zero_main e t n Z hZ hZ0 w hw hw0

variable {A : g32t_Sixfold}

theorem g32c_realization_aux (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    IsMonHom (g32c_incl X S hS) ∧ IsMonHom (g32c_proj X S hS) ∧
    g32c_incl X S hS ≫ g3_proj X.J (r + 1) 0 = fst A.X (g32c_B X S hS) ≫ X.inclA ∧
    (∀ j : Fin r, g32c_incl X S hS ≫ g3_proj X.J (r + 1) j.succ =
      snd A.X (g32c_B X S hS) ≫ cfd_proj r (g32c_parts X S hS) j ≫
        (X.part (S j) (hS j)).incl) ∧
    g32c_proj X S hS ≫ fst A.X (g32c_B X S hS) =
      g3_proj X.J (r + 1) 0 ≫ X.projA ≫ 𝟙 A.X ^ (g32c_N X S hS / X.NA) ∧
    (∀ j : Fin r, g32c_proj X S hS ≫ snd A.X (g32c_B X S hS) ≫
        cfd_proj r (g32c_parts X S hS) j =
      g3_proj X.J (r + 1) j.succ ≫ (X.part (S j) (hS j)).proj ≫
        𝟙 (g32c_parts X S hS j) ^ (g32c_N X S hS / (X.part (S j) (hS j)).N)) :=
  g32c_realization_main X S hS

theorem g32c_retraction_aux (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    0 < g32c_N X S hS ∧
    g32c_incl X S hS ≫ g32c_proj X S hS = 𝟙 (A.X ⊗ g32c_B X S hS) ^ g32c_N X S hS ∧
    ∀ n, homPullback (g32c_incl X S hS) n ∘ₗ homPullback (g32c_proj X S hS) n =
      ((g32c_N X S hS : ℚ) ^ n) • LinearMap.id :=
  g32c_retraction_main X S hS

end HodgeLean.Foundations.Program
