import HodgeLean.Foundations.Curves.CurveCycleClassDefs
import HodgeLean.Foundations.Curves.CubicS13
import HodgeLean.Foundations.Curves.CurveDegree
import HodgeLean.Foundations.Curves.CurveDivisors
import HodgeLean.Foundations.Curves.CurveDivisorClasses
import HodgeLean.RealDefs.PointClassConstant
import HodgeLean.RealDefs.ComplexFundamentalClass

/-! # Proofs for the frozen divisor cycle-class spec

Agreement on prime divisors unfolds the finite sum at the single point of `pointDivisor`
(`divisorCycleClass_pointDivisor_eq_primeDivisorClass`). The degree formula rewrites both the
cycle class and the degree as sums over the finite support, where every point is closed with
residue degree one, and uses `primeDivisorClass_eq_of_isClosed`; vanishing on principal divisors
and the cubic comparison of `[(0,0)]` and `[∞]` follow from it with `principalDivisors_le_ker_degree`
and `divisorDegree_pointDivisor`. The span statements follow from nonvanishing of a point class,
`span_singleton_eq_top_of_rank_le_one` and a closed point of the quasi-compact curve; on the cubic
the rank is `finrank_HQ_cubic`.

Equality of point classes (`primeDivisorClass_eq_of_isClosed`) is
`cycleComponentSheafClass_eq_of_coheight_eq` (`RealDefs/PointClassConstant.lean`): forgetting the
support factors through the full support, where it is injective; upstream's sheaf-to-singular
comparison commutes with enlarging the support (`RealDefs/SupportEnlargement.lean`); upstream's
exact point normalization turns the class into the pulled-back normalized point coclass; and a
global top homology class has the same coefficient against the complex orientation at every
point of the preconnected `X(ℂ)` (`RealDefs/OrientationConstant.lean`, through upstream's
orientation isomorphism of the homology sheaf with the constant sheaf).

Nonvanishing (`divisorCycleClass_pointDivisor_ne_zero_aux`) follows from
`cycleComponentSheafClass_ne_zero_of_fundamentalClass`: a fundamental class pairs to `1` with the
pulled-back point coclass. The fundamental class of the compact complex manifold `X(ℂ)`,
`exists_complexFundamentalClass_aux`, is `j5c_exists_complexFundamentalClass`
(`RealDefs/ComplexFundamentalClass.lean`), from Hatcher's Lemma 3.27.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs AlgebraicTopology.Singular

namespace HodgeLean.Foundations.Curves

/-- The divisor cycle class of `pointDivisor X.left P` is `primeDivisorClass X P`. -/
theorem divisorCycleClass_pointDivisor_eq_primeDivisorClass (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] [CompactSpace X.left] (P : X.left) :
    divisorCycleClass X (pointDivisor X.left P) = primeDivisorClass X P := by
  classical
  change ∑ᶠ Q, (pointDivisor X.left P : AlgebraicCycle X.left ℤ) Q • primeDivisorClass X Q = _
  by_cases h : Order.coheight P = 1
  · rw [finsum_eq_single _ P]
    · simp [pointDivisor_apply, h]
    · intro Q hQ
      simp [pointDivisor_apply, hQ]
  · have h0 : primeDivisorClass X P = 0 := by simp [primeDivisorClass, h]
    rw [h0]
    refine finsum_eq_zero_of_forall_eq_zero fun Q ↦ ?_
    simp [pointDivisor_apply, h]

/-- On a prime divisor, the divisor cycle class is upstream's cycle class. -/
theorem divisorCycleClass_pointDivisor_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [CompactSpace X.left] (P : X.left)
    (hP : Order.coheight P = ((1 : ℕ) : ℕ∞)) :
    divisorCycleClass X (pointDivisor X.left P) = cycleComponentSheafClass X P hP := by
  rw [divisorCycleClass_pointDivisor_eq_primeDivisorClass]
  exact dite_eq_left (hP.trans Nat.cast_one)

/-- The fundamental class of the compact complex manifold `X(ℂ)`: a class in
`H_{2d}(X(ℂ), ∅; ℚ)` whose local value at every complex point is upstream's complex orientation.
Source: Hatcher, *Algebraic Topology*, Theorem 3.26 and Lemma 3.27. -/
theorem exists_complexFundamentalClass_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    ∃ w : RelativeHomology ℚ (TopPair.ofSubset
        (((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ :
          Set (TopCat.of (ComplexPoint X)))) (2 * d),
      ∀ y : ComplexPoint X,
        relativeHomologyMap ℚ (2 * d)
            (supportInclusionPairMap (TopCat.of (ComplexPoint X))
              (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w =
          complexLocalOrientation X d y :=
  j5c_exists_complexFundamentalClass X d

/-- The class of a closed point of a curve is nonzero. -/
theorem divisorCycleClass_pointDivisor_ne_zero_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    [CompactSpace X.left] (P : X.left) (hP : IsClosed ({P} : Set X.left)) :
    divisorCycleClass X (pointDivisor X.left P) ≠ 0 := by
  have hP1 : Order.coheight P = ((1 : ℕ) : ℕ∞) :=
    (coheight_eq_one_of_isClosed X P hP).trans Nat.cast_one.symm
  obtain ⟨w, hw⟩ := exists_complexFundamentalClass_aux X 1
  rw [divisorCycleClass_pointDivisor_aux X P hP1]
  exact cycleComponentSheafClass_ne_zero_of_fundamentalClass X 1 P hP1 w hw

/-- On a connected curve, all closed points have the same prime divisor class. -/
theorem primeDivisorClass_eq_of_isClosed (hconn : ComplexPointsPreconnected)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProjective X.hom] (P Q : X.left) (hP : IsClosed ({P} : Set X.left))
    (hQ : IsClosed ({Q} : Set X.left)) :
    primeDivisorClass X P = primeDivisorClass X Q := by
  have := hconn.preconnected X
  have hP1 := coheight_eq_one_of_isClosed X P hP
  have hQ1 := coheight_eq_one_of_isClosed X Q hQ
  have eP : primeDivisorClass X P =
      cycleComponentSheafClass X P (p := 1) (hP1.trans Nat.cast_one.symm) := dite_eq_left hP1
  have eQ : primeDivisorClass X Q =
      cycleComponentSheafClass X Q (p := 1) (hQ1.trans Nat.cast_one.symm) := dite_eq_left hQ1
  rw [eP, eQ]
  exact cycleComponentSheafClass_eq_of_coheight_eq X 1 P Q _ _

/-- On a connected curve, the class of a divisor is its degree times the class of a point. -/
theorem divisorCycleClass_eq_degree_smul_aux (hconn : ComplexPointsPreconnected)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProjective X.hom] [CompactSpace X.left] (D : Divisor X.left) (P : X.left)
    (hP : IsClosed ({P} : Set X.left)) :
    divisorCycleClass X D = divisorDegree X D • divisorCycleClass X (pointDivisor X.left P) := by
  classical
  have hfin := (D : AlgebraicCycle X.left ℤ).finite_support
  have hclosed : ∀ Q, (D : AlgebraicCycle X.left ℤ) Q ≠ 0 → IsClosed ({Q} : Set X.left) :=
    fun Q hQ ↦ isClosed_of_coheight_eq_one (D.2 hQ)
  have hdeg : divisorDegree X D = ∑ᶠ Q, (D : AlgebraicCycle X.left ℤ) Q := by
    rw [divisorDegree, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
      AlgebraicCycle.degree_apply]
    refine finsum_congr fun Q ↦ ?_
    by_cases h0 : (D : AlgebraicCycle X.left ℤ) Q = 0
    · simp [h0]
    · rw [residueDegree_eq_one (hclosed Q h0), one_smul]
  change ∑ᶠ Q, (D : AlgebraicCycle X.left ℤ) Q • primeDivisorClass X Q = _
  rw [divisorCycleClass_pointDivisor_eq_primeDivisorClass, hdeg,
    finsum_eq_sum_of_support_subset _ (s := hfin.toFinset)
      (fun Q hQ ↦ by simpa using Function.support_smul_subset_left _ _ hQ),
    finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp), Finset.sum_smul]
  refine Finset.sum_congr rfl fun Q hQ ↦ ?_
  rw [primeDivisorClass_eq_of_isClosed hconn X Q P
    (hclosed Q (by simpa using hQ)) hP]

/-- On a connected curve, principal divisors have cycle class zero. -/
theorem principalDivisors_le_ker_divisorCycleClass_aux (hconn : ComplexPointsPreconnected)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProjective X.hom] [IsLocallyNoetherian X.left] [CompactSpace X.left] :
    principalDivisors X.left ≤ (divisorCycleClass X).ker := by
  intro D hD
  obtain ⟨P, -, hP⟩ := isClosed_univ.exists_closed_singleton (Set.univ_nonempty (α := X.left))
  rw [AddMonoidHom.mem_ker, divisorCycleClass_eq_degree_smul_aux hconn X D P hP,
    AddMonoidHom.mem_ker.mp (principalDivisors_le_ker_degree X hD), zero_smul]

/-- If `H²` of a curve is a line, the class of any closed point spans it. -/
theorem span_divisorCycleClass_pointDivisor_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    [CompactSpace X.left] (h : Module.finrank ℚ (HQ X 2) = 1) (P : X.left)
    (hP : IsClosed ({P} : Set X.left)) :
    Submodule.span ℚ {divisorCycleClass X (pointDivisor X.left P)} = ⊤ := by
  have : Module.Finite ℚ (HQ X 2) := Module.finite_of_finrank_eq_succ h
  refine span_singleton_eq_top_of_rank_le_one ?_
    (divisorCycleClass_pointDivisor_ne_zero_aux X P hP)
  rw [← Module.finrank_eq_rank, h]
  simp

/-- If `H²` of a curve is a line, the codimension-one cycle classes span it. -/
theorem algebraicCycleClassSpan_one_eq_top_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (h : Module.finrank ℚ (HQ X 2) = 1) :
    algebraicCycleClassSpan X 1 = ⊤ := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  obtain ⟨P, -, hP⟩ := isClosed_univ.exists_closed_singleton (Set.univ_nonempty (α := X.left))
  have h1 : Order.coheight P = ((1 : ℕ) : ℕ∞) :=
    (coheight_eq_one_of_isClosed X P hP).trans Nat.cast_one.symm
  have hs := span_divisorCycleClass_pointDivisor_aux X h P hP
  rw [divisorCycleClass_pointDivisor_aux X P h1] at hs
  exact eq_top_iff.mpr (hs.symm.le.trans (le_sSup ⟨P, h1, rfl⟩))

/-- The codimension-one cycle classes of the cubic span `H²(E(ℂ); ℚ)`. -/
theorem algebraicCycleClassSpan_one_cubic_aux : algebraicCycleClassSpan E 1 = ⊤ :=
  algebraicCycleClassSpan_one_eq_top_aux E (by rw [finrank_HQ_cubic]; rfl)

/-- `[(0,0)]` and `[∞]` have the same class in `H²(E(ℂ); ℚ)`. -/
theorem divisorCycleClass_finitePoint_eq_infinity_aux (hconn : ComplexPointsPreconnected) :
    divisorCycleClass E (pointDivisor E.left (finitePoint.base default)) =
      divisorCycleClass E (pointDivisor E.left cubicInfinity) := by
  rw [divisorCycleClass_eq_degree_smul_aux hconn E _ cubicInfinity cubicInfinity_isClosed,
    divisorDegree_pointDivisor _ finitePoint_isClosed, one_smul]

end HodgeLean.Foundations.Curves
