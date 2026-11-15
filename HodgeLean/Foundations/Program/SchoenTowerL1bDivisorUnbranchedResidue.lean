import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorLabelResidue
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIdentity
import HodgeLean.Foundations.Program.SchoenTowerL1bRotationCurveExpansion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- At a point with trivial stabilizer the original power equation has base order divisible by m. -/
theorem s2v_l1b_divisor_unbranched_residue
    (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [SmoothOfRelativeDimension 1 X.hom] [SmoothOfRelativeDimension 1 Y.hom]
    (G : Type) [Group G] [Finite G] {m : ℕ} (hm : m ≠ 0)
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left] [IsDominant q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hsurj : Function.Surjective (Point.map q))
    (horbit : ∀ x y : ComplexPoint X, Point.map q x = Point.map q y ↔
      ∃ g, Point.map (a g) x = y)
    (x : ComplexPoint X) (hfree : ∀ g, Point.map (a g) x = x ↔ g = 1)
    (u : X.left.functionField) (hu : u ≠ 0)
    (A B : Y.left.presheaf.stalk (q.left x.underlying)) (hA : A ≠ 0) (hB : B ≠ 0)
    (hpow : u ^ m = s2v_l1b_functionFieldPullback q.left
      (algebraMap _ Y.left.functionField A / algebraMap _ Y.left.functionField B))
    (p : Y.left.presheaf.stalk (q.left x.underlying)) (hprime : Prime p) :
    Int.ModEq (m : ℤ)
      (((emultiplicity p A).toNat : ℤ) - ((emultiplicity p B).toNat : ℤ)) 0 := by
  letI := s2e_smooth_curve_point_stalk_dvr X x
  letI : IsDiscreteValuationRing (Y.left.presheaf.stalk (q.left x.underlying)) := by
    simpa only [Point.underlying_map] using s2e_smooth_curve_point_stalk_dvr Y (Point.map q x)
  obtain ⟨ι, hι, hX, hc⟩ := s2v_l1b_rotation_curve_expansion X x
  obtain ⟨t, ht, htX⟩ := s2v_l1b_divisor_expansion_parameter ι
    (HodgeLean.Foundations.Curves.stalkC x.underlying) hc hX
  have hH (g : G) : Point.map (a g) x = x ↔ g ∈ (⊥ : Subgroup G) := by
    rw [hfree]; rfl
  have hclosed : IsClosed ({x.underlying} : Set X.left) := by
    haveI : IsClosedImmersion (x.left ≫ X.hom) := by
      rw [Over.w]
      change IsClosedImmersion (𝟙 (Spec ↧ℂ))
      infer_instance
    haveI : IsClosedImmersion x.left := IsClosedImmersion.of_comp x.left X.hom
    change IsClosed {x.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using x.left.isClosedMap
      {IsLocalRing.closedPoint ℂ} (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  let ξ := Complex.exp ((1 : ℂ) * (2 * Real.pi * Complex.I) / (m : ℂ))
  have hξ : IsPrimitiveRoot ξ m := by
    simpa only [ξ, Int.cast_one] using s2v_l1b_signed_character_primitive m hm 1 (Or.inl rfl)
  letI : IsIso (a 1).left := by
    change IsIso ((s2v_l1b_divisor_actionAut X G a ha1 hamul 1).asIso.hom.left)
    infer_instance
  have hid := s2v_l1b_divisor_identity_pullbacks X.left (a 1).left
    (congrArg Over.Hom.left ha1) x.underlying
    (s2e_complex_point_fixed_underlying X (a 1) x ((hH 1).mpr (by simp)))
  have hcomp : ∀ v, ι (s2e_fixed_point_stalkPullback X.left (a 1).left x.underlying
      (s2e_complex_point_fixed_underlying X (a 1) x ((hH 1).mpr (by simp))) v) =
        PowerSeries.rescale (ξ ^ m) (ι v) := by
    intro v
    rw [hid.1, hξ.pow_eq_one, PowerSeries.rescale_one]
    rfl
  apply s2v_l1b_divisor_curve_residue X Y G a ha1 hamul q hinv
    (s2v_l1b_divisor_original_quotient X Y G a ha1 hamul q hsurj hinv horbit)
    x hclosed ⊥ hH ι hι t ht htX 1 (by simp) ξ hm (by simp) hξ hcomp
    (HodgeLean.Foundations.Curves.stalkC x.underlying (ξ ^ 0)) (hc _) u hu
    (by
      rw [hid.2]
      simp only [pow_zero, map_one, one_mul]
      rfl)
    A B hA hB hpow p hprime

end HodgeLean.Foundations.Program
