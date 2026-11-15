import HodgeLean.Foundations.Program.SchoenTransferDefs
import HodgeLean.Foundations.Program.CycleFoundations

/-! Bilinearity and separated-kernel evaluation for correspondence actions. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
open scoped BigOperators
attribute [local irreducible] cupProductOf homPullback algebraicCycleClassSpan
namespace HodgeLean.Foundations.Program

theorem s4_corrAction_add
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q : ℕ)
    (h : 2 * c + 2 * p = 2 * q + 2 * d)
    (ξ η : HQ (A ⊗ B) (2 * c)) :
    cfd_corrAction A B d I c p q h (ξ + η) =
      cfd_corrAction A B d I c p q h ξ + cfd_corrAction A B d I c p q h η := by
  ext x
  simp only [cfd_corrAction, LinearMap.comp_apply, map_add, LinearMap.add_apply]

theorem s4_corrAction_smul
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q : ℕ)
    (h : 2 * c + 2 * p = 2 * q + 2 * d)
    (a : ℚ) (ξ : HQ (A ⊗ B) (2 * c)) :
    cfd_corrAction A B d I c p q h (a • ξ) =
      a • cfd_corrAction A B d I c p q h ξ := by
  ext x
  simp only [cfd_corrAction, LinearMap.comp_apply, map_smul, LinearMap.smul_apply]

/-- Correspondence classes map linearly to their cohomological operators. -/
def s4_corrActionLinear
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q : ℕ)
    (h : 2 * c + 2 * p = 2 * q + 2 * d) :
    HQ (A ⊗ B) (2 * c) →ₗ[ℚ] (HQ B (2 * p) →ₗ[ℚ] HQ A (2 * q)) where
  toFun := cfd_corrAction A B d I c p q h
  map_add' := s4_corrAction_add A B d I c p q h
  map_smul' := s4_corrAction_smul A B d I c p q h

theorem s4_corrAction_cross
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (g k : ℕ) (hdim : TopologicalSpace.dim B.left = g) (hk : k ≤ g)
    (I : HQ B (2 * g) ≃ₗ[ℚ] ℚ) (a : HQ A (2 * k)) (b : HQ B (2 * k))
    (x : HQ B (2 * (g - k))) :
    cfd_corrAction A B g I (2 * k) (g - k) k (by omega)
      ((cupProductOf (A ⊗ B)).cup (by omega)
        (homPullback (fst A B) (2 * k) a) (homPullback (snd A B) (2 * k) b)) x =
      I ((cupProductOf B).cup (by omega) b x) • a := by
  change cfd_projection A B g I (2 * k)
    ((cupProductOf (A ⊗ B)).cup (by omega)
      ((cupProductOf (A ⊗ B)).cup (by omega)
        (homPullback (fst A B) (2 * k) a) (homPullback (snd A B) (2 * k) b))
      (homPullback (snd A B) (2 * (g - k)) x)) = _
  rw [(cupProductOf (A ⊗ B)).assoc (by omega)
    (show 2 * k + 2 * (g - k) = 2 * g by omega) (by omega) rfl,
    ← spec_homPullback_cup (snd A B) (show 2 * k + 2 * (g - k) = 2 * g by omega),
    cfd_projection_cross A B g hdim I (2 * k)]

/-- A separated kernel contracts its source factor against the top coordinate. -/
theorem s4_corrAction_cross_degree
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hdim : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q v : ℕ)
    (h : 2 * c + 2 * p = 2 * q + 2 * d)
    (hv : v + 2 * p = 2 * d) (hc : 2 * q + v = 2 * c)
    (a : HQ A (2 * q)) (b : HQ B v) (x : HQ B (2 * p)) :
    cfd_corrAction A B d I c p q h
      ((cupProductOf (A ⊗ B)).cup hc
        (homPullback (fst A B) (2 * q) a) (homPullback (snd A B) v b)) x =
      I ((cupProductOf B).cup hv b x) • a := by
  change cfd_projection A B d I (2 * q)
    ((cupProductOf (A ⊗ B)).cup h
      ((cupProductOf (A ⊗ B)).cup hc
        (homPullback (fst A B) (2 * q) a) (homPullback (snd A B) v b))
      (homPullback (snd A B) (2 * p) x)) = _
  rw [(cupProductOf (A ⊗ B)).assoc hc hv h rfl,
    ← spec_homPullback_cup (snd A B) hv,
    cfd_projection_cross A B d hdim I (2 * q)]

/-- A separated kernel has zero action unless its source degree reaches the top. -/
theorem s4_corrAction_cross_off
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q u v : ℕ)
    (h : 2 * c + 2 * p = 2 * q + 2 * d)
    (hc : u + v = 2 * c) (hv : v + 2 * p ≠ 2 * d)
    (a : HQ A u) (b : HQ B v) (x : HQ B (2 * p)) :
    cfd_corrAction A B d I c p q h
      ((cupProductOf (A ⊗ B)).cup hc
        (homPullback (fst A B) u a) (homPullback (snd A B) v b)) x = 0 := by
  change cfd_projection A B d I (2 * q)
    ((cupProductOf (A ⊗ B)).cup h
      ((cupProductOf (A ⊗ B)).cup hc
        (homPullback (fst A B) u a) (homPullback (snd A B) v b))
      (homPullback (snd A B) (2 * p) x)) = 0
  rw [(cupProductOf (A ⊗ B)).assoc hc rfl h (by omega),
    ← spec_homPullback_cup (snd A B) rfl,
    cfd_projection_cross_off A B d I (2 * q) u (v + 2 * p) (by omega) hv]

theorem s4_corrAction_sum
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q : ℕ)
    (h : 2 * c + 2 * p = 2 * q + 2 * d)
    {ι : Type*} (s : Finset ι) (ξ : ι → HQ (A ⊗ B) (2 * c)) :
    cfd_corrAction A B d I c p q h (∑ i ∈ s, ξ i) =
      ∑ i ∈ s, cfd_corrAction A B d I c p q h (ξ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext x
      simp only [Finset.sum_empty, cfd_corrAction, LinearMap.comp_apply,
        map_zero, LinearMap.zero_apply]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, s4_corrAction_add, ih]

end HodgeLean.Foundations.Program
