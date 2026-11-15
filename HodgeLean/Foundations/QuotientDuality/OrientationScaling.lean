import HodgeLean.Foundations.QuotientDuality.OrientationDefs

/-! Scalar changes of local orientation generators. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma orientationLine_smul (X : TopCat.{0}) (n : ℕ) (c : Homology ℚ X n)
    (x : X) (a r : ℚ) :
    orientationLine X n (a • c) x r = a • orientationLine X n c x r := by
  change r • ((relativeHomologyProjection ℚ (pointComplementPair x) n).hom (a • c)) =
    a • (r • ((relativeHomologyProjection ℚ (pointComplementPair x) n).hom c))
  rw [map_smul, smul_comm]

lemma orientationLine_smul_bijective (X : TopCat.{0}) (n : ℕ) (c : Homology ℚ X n)
    (x : X) (a : ℚ) (ha : a ≠ 0)
    (h : Function.Bijective (orientationLine X n c x)) :
    Function.Bijective (orientationLine X n (a • c) x) := by
  have he : orientationLine X n (a • c) x =
      (LinearEquiv.smulOfNeZero ℚ (orientationGroup X n x) a ha).toLinearMap.comp (orientationLine X n c x) := by
    apply LinearMap.ext
    intro r
    exact orientationLine_smul X n c x a r
  rw [he]
  exact (LinearEquiv.smulOfNeZero ℚ (orientationGroup X n x) a ha).bijective.comp h

lemma normalized_pushforward_generators (G : Type) [Group G] (X : TopCat.{0})
    [MulAction G X] (n : ℕ) (cX : Homology ℚ X n) (d : ℕ) (hd : 0 < d)
    (hlocal : ∀ y, Function.Bijective
      (orientationLine (orbitSpace G X) n (homologyMap ℚ n (orbitMap G X) cX) y)) :
    ∃ cY : Homology ℚ (orbitSpace G X) n,
      homologyMap ℚ n (orbitMap G X) cX = (d : ℚ) • cY ∧
      ∀ y, Function.Bijective (orientationLine (orbitSpace G X) n cY y) := by
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  refine ⟨(d : ℚ)⁻¹ • homologyMap ℚ n (orbitMap G X) cX, ?_, ?_⟩
  · rw [smul_smul, mul_inv_cancel₀ hdQ, one_smul]
  · intro y
    exact orientationLine_smul_bijective _ n _ y _ (inv_ne_zero hdQ) (hlocal y)

lemma localOrientation_ne_zero (X : TopCat.{0}) (n : ℕ) (c : Homology ℚ X n)
    (x : X) (h : Function.Injective (orientationLine X n c x)) :
    localOrientation X n c x ≠ 0 := by
  intro hz
  have he : orientationLine X n c x (1 : ℚ) = orientationLine X n c x (0 : ℚ) := by
    change (1 : ℚ) • localOrientation X n c x = (0 : ℚ) • localOrientation X n c x
    rw [hz, smul_zero, smul_zero]
  exact one_ne_zero (h he)

end HodgeLean.Foundations.QuotientDuality
