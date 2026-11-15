import HodgeLean.Foundations.Program.SchoenTransferLefschetzKernel
import HodgeLean.Foundations.Program.SchoenTransferDegreeZero
import HodgeLean.Foundations.Program.SchoenTransferLinear
import HodgeLean.Foundations.Program.SchoenTransferDefs
import HodgeLean.Foundations.Program.SchoenSelectedGeometry

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Papers
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program

/-- Degree-one pullback of a group sum from a smooth projective source. -/
theorem s4_homPullback_mul
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (T : Over (Spec ↧ℂ)) [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (f g : T ⟶ A) :
    homPullback (f * g) 1 = homPullback f 1 + homPullback g 1 := by
  let u : T ⟶ A ⊗ A := CartesianMonoidalCategory.lift f g
  have hm := spec_homPullback_mul
    (CartesianMonoidalCategory.fst A A) (CartesianMonoidalCategory.snd A A)
  have hcomp : u ≫ (CartesianMonoidalCategory.fst A A *
      CartesianMonoidalCategory.snd A A) = f * g := by
    rw [MonObj.comp_mul, CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.lift_snd]
  rw [← hcomp, spec_homPullback_comp, hm, LinearMap.comp_add,
    ← spec_homPullback_comp, ← spec_homPullback_comp,
    CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]

/-- The constant group identity has zero pullback in degree one. -/
theorem s4_homPullback_one
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (T : Over (Spec ↧ℂ)) [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom] :
    homPullback (1 : T ⟶ A) 1 = 0 := by
  have hh := s4_homPullback_mul A T (1 : T ⟶ A) 1
  rw [one_mul] at hh
  exact (add_left_cancel (show homPullback (1 : T ⟶ A) 1 + 0 =
    homPullback (1 : T ⟶ A) 1 + homPullback (1 : T ⟶ A) 1 by
      rw [add_zero]; exact hh)).symm

/-- Pullback of the actual curve sum is the sum of coordinate pullbacks in degree one. -/
theorem s4_sum_pullback_one
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom] :
    homPullback (s4_sum f n) 1 =
      ∑ i : Fin n, (homPullback (g3_proj Y n i) 1).comp (homPullback f 1) := by
  classical
  unfold s4_sum
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, s4_homPullback_one]
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, s4_homPullback_mul, ih,
        spec_homPullback_comp]

/-- Coordinate permutations preserve the actual sum morphism. -/
theorem s4_sum_permute
    {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
    (f : Y ⟶ A) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    s2_permute Y n σ ≫ s4_sum f n = s4_sum f n := by
  classical
  have hproj {T : Over (Spec ↧ℂ)} (n : ℕ)
      (u : Fin n → (T ⟶ Y)) (i : Fin n) :
      s2_lift n u ≫ g3_proj Y n i = u i := by
    induction n with
    | zero => exact Fin.elim0 i
    | succ n ih =>
        refine Fin.cases ?_ (fun j => ?_) i
        · exact CartesianMonoidalCategory.lift_fst _ _
        · change CartesianMonoidalCategory.lift _ _ ≫
            (CartesianMonoidalCategory.snd _ _ ≫ g3_proj Y n j) = _
          rw [← Category.assoc, CartesianMonoidalCategory.lift_snd]
          exact ih _ j
  let R : (g3_power Y n ⟶ A) →* (g3_power Y n ⟶ A) :=
    { toFun := fun u => s2_permute Y n σ ≫ u
      map_one' := MonObj.comp_one _
      map_mul' := MonObj.comp_mul _ }
  change R (∏ i : Fin n, g3_proj Y n i ≫ f) =
    ∏ i : Fin n, g3_proj Y n i ≫ f
  rw [map_prod]
  change (∏ i : Fin n, s2_permute Y n σ ≫ (g3_proj Y n i ≫ f)) = _
  simp only [← Category.assoc, s2_permute, hproj]
  exact σ.symm.prod_comp (fun i => g3_proj Y n i ≫ f)

/-- Every class pulled back by the sum is fixed by coordinate permutations. -/
theorem s4_sum_pullback_permute
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (Y : Over (Spec ↧ℂ)) (f : Y ⟶ A) (n d : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom]
    (σ : Equiv.Perm (Fin n)) (x : HQ A d) :
    homPullback (s2_permute Y n σ) d (homPullback (s4_sum f n) d x) =
      homPullback (s4_sum f n) d x := by
  rw [← LinearMap.comp_apply, ← spec_homPullback_comp, s4_sum_permute]

section

attribute [local irreducible] cupProductOf homPullback algebraicCycleClassSpan
  cfd_corrAction cfd_projection lefschetzPow
set_option maxHeartbeats 200000

theorem s4_inverse_lefschetz_aux (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g k : ℕ) (hdim : TopologicalSpace.dim A.left = g) (hk : 2 * k ≤ g)
    (I : HQ A (2 * g) ≃ₗ[ℚ] ℚ) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη) :
    ∃ ξ : HQ (A ⊗ A) (2 * (2 * k)), ξ ∈ cfd_cycleSpan (A ⊗ A) (2 * k) ∧
      ∀ x : HQ A (2 * k),
        cfd_corrAction A A g I (2 * k) (g - k) k (by omega) ξ
          (lefschetzPow A (cupProductOf A) pol (g - 2 * k) (by omega) x) = x := by
  cases k with
  | zero =>
    simpa only [Nat.mul_zero, Nat.sub_zero] using
      s4_inverse_lefschetz_zero A g hdim I pol hη
  | succ k =>
    have hpol := s4_positive_polarization_mem_cycleSpan A pol hη hpos
    apply s4_inverse_lefschetz_of_injective_kernel A g (k + 1) hdim hk I pol hpol
      (s4_mixedKernel A pol (k + 1)) (s4_mixedKernel_mem A pol hpol (k + 1))
    let L := lefschetzPow A (cupProductOf A) pol (g - 2 * (k + 1))
      (k := 2 * (k + 1)) (m := 2 * (g - (k + 1))) (by omega)
    have hL := (hardLefschetz_abelian A hη).bijective
      (k := 2 * (k + 1)) (m := 2 * (g - (k + 1))) (by omega) (by omega)
    have hLi : Function.Injective L := by
      simpa only [hdim] using hL.1
    have hKi := s4_mixedKernel_action_injective A g (k + 1) hdim (by omega) I pol hη
    intro x y hxy
    apply hLi
    apply hKi
    exact hxy


/-- Algebraicity of the Lefschetz image reflects through its algebraic inverse.
Source: Kleiman, Algebraic cycles and the Weil conjectures, §2; Fulton, §16.1. -/
theorem s4_lefschetz_reflects_algebraic
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g k : ℕ) (hdim : TopologicalSpace.dim A.left = g) (hk : 2 * k ≤ g)
    (I : HQ A (2 * g) ≃ₗ[ℚ] ℚ) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
    (x : HQ A (2 * k))
    (hx : lefschetzPow A (cupProductOf A) pol (g - 2 * k) (by omega) x ∈
      cfd_cycleSpan A (g - k)) :
    x ∈ cfd_cycleSpan A k := by
  obtain ⟨ξ, hξ, hξx⟩ := s4_inverse_lefschetz_aux A g k hdim hk I pol hη hpos
  rw [← hξx x]
  exact cfd_correspondence_span A A g hdim I (2 * k) (g - k) k
    (by omega) ξ hξ _ hx

end

/-- An inverse Lefschetz operator represented by an algebraic correspondence class.
Source: Lieberman (1968), Theorem 3; Schoen (1988), proof of Corollary 3.1, p. 25. -/
theorem s4_inverse_lefschetz (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g k : ℕ) (hdim : TopologicalSpace.dim A.left = g) (hk : 2 * k ≤ g)
    (I : HQ A (2 * g) ≃ₗ[ℚ] ℚ) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη) :
    ∃ ξ : HQ (A ⊗ A) (2 * (2 * k)), ξ ∈ cfd_cycleSpan (A ⊗ A) (2 * k) ∧
      ∀ x : HQ A (2 * k),
        cfd_corrAction A A g I (2 * k) (g - k) k (by omega) ξ
          (lefschetzPow A (cupProductOf A) pol (g - 2 * k) (by omega) x) = x :=
  s4_inverse_lefschetz_aux A g k hdim hk I pol hη hpos

example := @s4_inverse_lefschetz


end HodgeLean.Foundations.Program
