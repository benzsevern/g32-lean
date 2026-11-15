import HodgeLean.Foundations.Program.SchoenTransferComposition
import HodgeLean.Adapters.HodgeOpposedAbelianProofs
import HodgeLean.Foundations.Program.SchoenTransferDefs

/-! Perfect rational cup pairing in the supplied top coordinate. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
attribute [local irreducible] cupProductOf homPullback algebraicCycleClassSpan
namespace HodgeLean.Foundations.Program

theorem s4_cupPairing_bijective
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g : ℕ) (hdim : TopologicalSpace.dim A.left = g)
    (i j : ℕ) (h : i + j = 2 * g) (I : HQ A (2 * g) ≃ₗ[ℚ] ℚ) :
    Function.Bijective (((cupProductOf A).cup h).compr₂ I.toLinearMap) := by
  subst g
  letI := (finiteBetti_abelian A).finite i
  let P := ((cupProductOf A).cup h).compr₂ I.toLinearMap
  have hleft : Function.Injective P := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply cup_eq_zero_of_forall_cup_eq_zero_torus (torusCohomology_cupProductOf A) h x
    intro y
    apply I.injective
    have hy := LinearMap.congr_fun hx y
    simpa only [P, LinearMap.compr₂_apply, LinearMap.zero_apply, LinearEquiv.coe_coe, map_zero] using hy
  have hright : Function.Injective P.flip := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply cup_eq_zero_of_forall_cup_eq_zero_torus (torusCohomology_cupProductOf A)
      (show j + i = 2 * TopologicalSpace.dim A.left by omega) x
    intro y
    have hzero : (cupProductOf A).cup h y x = 0 := by
      apply I.injective
      have hy := LinearMap.congr_fun hx y
      simpa only [P, LinearMap.flip_apply, LinearMap.compr₂_apply,
        LinearMap.zero_apply, LinearEquiv.coe_coe, map_zero] using hy
    rw [(cupProductOf A).graded_comm h (by omega), hzero, smul_zero]
  exact (LinearMap.IsPerfPair.of_injective hleft hright).bijective_left

/-- The actual Künneth map in a single specified bidegree. -/
def s4_crossMap
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (p q m : ℕ) (h : p + q = m) :
    HQ A p ⊗[ℚ] HQ B q →ₗ[ℚ] HQ (A ⊗ B) m :=
  TensorProduct.lift (((cupProductOf (A ⊗ B)).cup h).compl₁₂
    (homPullback (fst A B) p) (homPullback (snd A B) q))

/-- Evaluation of the single-bidegree Künneth map on a pure tensor. -/
theorem s4_crossMap_tmul
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (p q m : ℕ) (h : p + q = m) (a : HQ A p) (b : HQ B q) :
    s4_crossMap A B p q m h (a ⊗ₜ[ℚ] b) =
      (cupProductOf (A ⊗ B)).cup h
        (homPullback (fst A B) p a) (homPullback (snd A B) q b) := rfl

/-- Exchange the middle two factors of a fourfold cup product. -/
theorem s4_cup_middle_exchange
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (P : CupProduct X) (u v s t m n p q l : ℕ)
    (huv : u + v = m) (hst : s + t = n)
    (hp : u + s = p) (hq : v + t = q) (hl : m + n = l)
    (a : HQ X u) (b : HQ X v) (c : HQ X s) (e : HQ X t) :
    P.cup hl (P.cup huv a b) (P.cup hst c e) =
      ((-1 : ℚ) ^ (v * s)) • P.cup (show p + q = l by omega)
        (P.cup hp a c) (P.cup hq b e) := by
  subst m
  subst n
  subst p
  subst q
  subst l
  rw [← P.assoc (show (u + v) + s = (u + s) + v by omega) rfl
      (by omega) rfl (P.cup rfl a b) c e,
    s4_cup_right_exchange X P u v s a b c,
    map_smul, LinearMap.smul_apply,
    P.assoc rfl rfl (by omega) (by omega) (P.cup rfl a c) b e]

/-- Products of Künneth bidegrees add the two factor degrees separately. -/
theorem s4_crossMap_cup_mem
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (u v s t m n p q l : ℕ)
    (huv : u + v = m) (hst : s + t = n)
    (hp : u + s = p) (hq : v + t = q) (hl : m + n = l)
    (x : HQ (A ⊗ B) m) (y : HQ (A ⊗ B) n)
    (hx : x ∈ LinearMap.range (s4_crossMap A B u v m huv))
    (hy : y ∈ LinearMap.range (s4_crossMap A B s t n hst)) :
    (cupProductOf (A ⊗ B)).cup hl x y ∈
      LinearMap.range (s4_crossMap A B p q l (by omega)) := by
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
          rw [s4_crossMap_tmul, s4_crossMap_tmul,
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

/-- Projection integration detects zero on the top-source Künneth bidegree. -/
theorem s4_projection_zero_on_cross
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hdim : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (n : ℕ)
    (z : HQ (A ⊗ B) (n + 2 * d))
    (hz : z ∈ LinearMap.range (s4_crossMap A B n (2 * d) (n + 2 * d) rfl))
    (hzero : cfd_projection A B d I n z = 0) : z = 0 := by
  let E := (TensorProduct.congr (LinearEquiv.refl ℚ (HQ A n)) I).trans
    (TensorProduct.rid ℚ (HQ A n))
  have he : (cfd_projection A B d I n).comp
      (s4_crossMap A B n (2 * d) (n + 2 * d) rfl) = E.toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    change cfd_projection A B d I n
      (s4_crossMap A B n (2 * d) (n + 2 * d) rfl (a ⊗ₜ[ℚ] b)) = E (a ⊗ₜ[ℚ] b)
    rw [s4_crossMap_tmul, cfd_projection_cross A B d hdim I n]
    rfl
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hz
  change ((cfd_projection A B d I n).comp
    (s4_crossMap A B n (2 * d) (n + 2 * d) rfl)) w = 0 at hzero
  rw [he] at hzero
  have hw : w = 0 := E.injective (hzero.trans E.map_zero.symm)
  rw [hw, map_zero]

/-- Powers of a class in bidegree one-one remain in the matching diagonal bidegree. -/
theorem s4_lefschetzPow_mem_cross
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (θ : HQ (A ⊗ B) 2)
    (hθ : θ ∈ LinearMap.range (s4_crossMap A B 1 1 2 rfl)) (r : ℕ) :
    lefschetzPow (A ⊗ B) (cupProductOf (A ⊗ B)) θ r (by omega) (cupUnit (A ⊗ B)) ∈
      LinearMap.range (s4_crossMap A B r r (2 * r) (by omega)) := by
  induction r with
  | zero =>
      change cupUnit (A ⊗ B) ∈ LinearMap.range (s4_crossMap A B 0 0 0 rfl)
      refine LinearMap.mem_range.mpr ⟨cupUnit A ⊗ₜ[ℚ] cupUnit B, ?_⟩
      rw [s4_crossMap_tmul, spec_homPullback_unit, spec_homPullback_unit]
      exact (cupProductOf (A ⊗ B)).one_cup (cupUnit (A ⊗ B))
  | succ r ih =>
      rw [lefschetzPow_succ (cupProductOf (A ⊗ B)) θ r _
        (show 0 + 2 * r = 2 * r by omega) (by omega)]
      exact s4_crossMap_cup_mem A B 1 1 r r 2 (2 * r) (r + 1) (r + 1) (2 * (r + 1))
        rfl (by omega) (by omega) (by omega) (by omega) θ _ hθ ih

end HodgeLean.Foundations.Program
