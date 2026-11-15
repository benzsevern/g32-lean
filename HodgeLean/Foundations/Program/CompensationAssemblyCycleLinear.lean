import HodgeLean.Foundations.Program.CompensationAssemblyPullback

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

theorem cq_cycleClass_zero (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (q : ℕ) :
    (ccm3_cycleClass X q 0 : HQ X (2 * q)) = 0 := by
  unfold ccm3_cycleClass
  apply finsum_eq_zero_of_forall_eq_zero
  intro z
  change (0 : ℚ) • cycleComponentSheafClass X z.1 z.2 = 0
  exact zero_smul _ _

def cq_cycleClassAddHom (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (q : ℕ) :
    AlgebraicCycle X.left ℚ →+ HQ X (2*q) where
  toFun := ccm3_cycleClass X q
  map_zero' := cq_cycleClass_zero X q
  map_add' c d := (ccm6_cycleClass_linear_aux X q 0 c d).1

theorem cq_cycle_hom_ext_pure {X : Scheme} [CompactSpace X]
    {V : Type*} [AddCommMonoid V] [DecidableEq X] (p : ℕ)
    (L R : AlgebraicCycle X ℚ →+ V)
    (hgen : ∀ (x : X), Order.coheight x = p → ∀ r : ℚ,
      L ((Function.locallyFinsuppWithin.single x r).restrict (Set.subset_univ _)) =
        R ((Function.locallyFinsuppWithin.single x r).restrict (Set.subset_univ _)))
    (c : AlgebraicCycle X ℚ) (hc : ∀ x, c x ≠ 0 → Order.coheight x = p) :
    L c = R c := by
  classical
  let g : X → AlgebraicCycle X ℚ := fun x =>
    (Function.locallyFinsuppWithin.single x (c x)).restrict (Set.subset_univ _)
  have hsum : ∑ᶠ x, g x = c :=
    Function.locallyFinsuppWithin.sum_apply_smul_single_eq_self c.finite_support
  rw [← hsum]
  apply finsum_induction (p := fun d => L d = R d)
  · rw [map_zero, map_zero]
  · intro d e hd he
    rw [map_add, map_add, hd, he]
  · intro x
    by_cases hx : c x = 0
    · have hg : g x = 0 := by
        apply Function.locallyFinsuppWithin.ext
        intro z
        simp only [g, Function.locallyFinsuppWithin.restrict_apply, Set.mem_univ,
          ↓reduceIte, Function.locallyFinsuppWithin.single_apply, hx, ite_self,
          Pi.zero_apply]
        rfl
      rw [hg, map_zero, map_zero]
    · exact hgen x (hc x hx) (c x)

theorem cq_single_mapRange (X : Scheme) [DecidableEq X] (x : X) (r : ℚ) :
    ((Function.locallyFinsuppWithin.single x r).restrict (Set.subset_univ _) : AlgebraicCycle X ℚ) =
      ((Function.locallyFinsuppWithin.single x (1 : ℚ)).restrict (Set.subset_univ _)).mapRange
        (r * ·) (mul_zero r) := by
  apply Function.locallyFinsuppWithin.ext
  intro z
  simp only [Function.locallyFinsuppWithin.restrict_apply,
    Function.locallyFinsuppWithin.mapRange_apply, Set.mem_univ, ↓reduceIte,
    Function.locallyFinsuppWithin.single_apply]
  by_cases hz : z = x
  · simp only [hz, ↓reduceIte, mul_one]
  · simp only [hz, ↓reduceIte, mul_zero]

theorem cq_pushforward_cycleClass_single_smul {X Z : Over (Spec ↧ℂ)}
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [QuasiCompact f.left] [DecidableEq X.left]
    (q : ℕ) (x : X.left) (r : ℚ) :
    ccm3_cycleClass Z q (a1p_pushforward f.left
      ((Function.locallyFinsuppWithin.single x r).restrict (Set.subset_univ _))) =
    r • ccm3_cycleClass Z q (a1p_pushforward f.left
      ((Function.locallyFinsuppWithin.single x (1 : ℚ)).restrict (Set.subset_univ _))) := by
  rw [cq_single_mapRange X.left x r, a1p_pushforward_mul]
  exact (ccm6_cycleClass_linear_aux Z q r _ 0).2

theorem cq_cycle_single_wrong_codimension {X : Over (Spec ↧ℂ)}
    [DecidableEq X.left]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (x : X.left) (hx : Order.coheight x ≠ q) (a : ℚ) :
    ccm3_cycleClass X q
      ((Function.locallyFinsuppWithin.single x a).restrict (Set.subset_univ _)) = 0 := by
  unfold ccm3_cycleClass
  apply finsum_eq_zero_of_forall_eq_zero
  intro z
  have hzx : z.1 ≠ x := fun h => hx (h ▸ z.2)
  simp only [Function.locallyFinsuppWithin.restrict_apply, Set.mem_univ,
    ↓reduceIte, Function.locallyFinsuppWithin.single_apply, if_neg hzx, zero_smul]
  rfl

theorem cq_single_restrict_univ (X : Scheme) [DecidableEq X] (x : X) (r : ℚ) :
    ((Function.locallyFinsuppWithin.single x r).restrict (Set.subset_univ _) :
      AlgebraicCycle X ℚ) = Function.locallyFinsuppWithin.single x r := by
  ext z
  simp only [Function.locallyFinsuppWithin.restrict_apply, Set.mem_univ, ↓reduceIte]

theorem cq_pushforward_prime_class {X Z : Over (Spec ↧ℂ)}
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [QuasiCompact f.left] [DecidableEq X.left] [DecidableEq Z.left]
    (q : ℕ) (x : X.left) (hx : Order.coheight (f.left x) = q) (r : ℚ) :
    ccm3_cycleClass Z q (a1p_pushforward f.left
      ((Function.locallyFinsuppWithin.single x r).restrict (Set.subset_univ _))) =
      (r * (a1p_degree f.left x : ℚ)) •
        (cycleComponentSheafClass Z (f.left x) hx : HQ Z (2 * q)) := by
  rw [cq_single_restrict_univ, a1p_pushforward_single,
    ← cq_single_restrict_univ Z.left (f.left x)]
  exact cq_cycle_single_eq q (f.left x) hx _

theorem cq_pushforward_prime_class_wrong_codimension {X Z : Over (Spec ↧ℂ)}
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [QuasiCompact f.left] [DecidableEq X.left] [DecidableEq Z.left]
    (q : ℕ) (x : X.left) (hx : Order.coheight (f.left x) ≠ q) (r : ℚ) :
    ccm3_cycleClass Z q (a1p_pushforward f.left
      ((Function.locallyFinsuppWithin.single x r).restrict (Set.subset_univ _))) = 0 := by
  rw [cq_single_restrict_univ, a1p_pushforward_single,
    ← cq_single_restrict_univ Z.left (f.left x)]
  exact cq_cycle_single_wrong_codimension q (f.left x) hx _

theorem cq_pushforward_prime_class_formula {X Z : Over (Spec ↧ℂ)}
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [QuasiCompact f.left] [DecidableEq X.left] [DecidableEq Z.left]
    (q : ℕ) (x : X.left) (r : ℚ) :
    ccm3_cycleClass Z q (a1p_pushforward f.left
      ((Function.locallyFinsuppWithin.single x r).restrict (Set.subset_univ _))) =
      (if hx : Order.coheight (f.left x) = q then
        (r * (a1p_degree f.left x : ℚ)) •
          (cycleComponentSheafClass Z (f.left x) hx : HQ Z (2 * q))
      else 0) := by
  classical
  by_cases hx : Order.coheight (f.left x) = q
  · rw [dif_pos hx]
    exact cq_pushforward_prime_class f q x hx r
  · rw [dif_neg hx]
    exact cq_pushforward_prime_class_wrong_codimension f q x hx r

end HodgeLean.Foundations.Program
