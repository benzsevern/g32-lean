import HodgeLean.Foundations.Program.SchoenCyclePushDefs
import HodgeLean.Foundations.Program.S2P1bc
import HodgeLean.Foundations.Program.SchoenCycleDualityHelpers
import HodgeLean.Foundations.QuotientDuality.P1bMiddlePerfect
import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientCohomology

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.QuotientDuality
open HodgeLean.Foundations.Analytic
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- The actual cup pairing attached to a projective local orientation. -/
theorem g32n_projective_cup_perfect
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (n : ℕ) (hn : 0 < n)
    (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (n + n))
    (c : Homology ℚ (TopCat.of (ComplexPoint X)) (n + n))
    (hc : ∀ x, localOrientation _ _ c x = o.generator x) :
    Function.Bijective ((HodgeLean.Foundations.Singular.cup
      (TopCat.of (ComplexPoint X)) (rfl : n + n = n + n)).compr₂
      (orientationIntegral _ _ c)) := by
  obtain ⟨N, f, ⟨e⟩⟩ := s4_selected_projective_boolean_model X
  obtain ⟨T⟩ := s4_selected_boolean_finite_triangulation
    (TopCat.of (ComplexPoint X)) N f e
  obtain ⟨M, _⟩ := HodgeLean.Foundations.IntegralHomology.StageTwo.triangulated_model_aux
    T.ambient T.complex T.finite_faces
  letI := finiteModel_rational_cohomology _
    (M.transport (TopCat.isoOfHomeo T.realization)) n
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  have hpair : (HodgeLean.Foundations.Singular.cup
      (TopCat.of (ComplexPoint X)) (rfl : n + n = n + n)).compr₂
      (orientationIntegral _ _ c) =
      localTracePairing (TopCat.of (ComplexPoint X)) n n c := by
    ext u v
    dsimp only [LinearMap.compr₂_apply]
    rw [← localTraceCup_eq_singularCup]
    change cohomologyEquivDualHomology ℚ _ _
      ((cohomologyEquivDualHomology ℚ _ _).symm _) c = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [hpair]
  apply localTracePairing_bijective_of_cap _ n c
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact HodgeLean.Foundations.RationalHomologyManifold.cap_positive _ T m m o c (funext hc)

/-- Degree transport for the actual cup pairing. -/
theorem g32n_projective_cup_perfect_degree
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (n d : ℕ) (hn : 0 < n) (hd : n + n = d) :
    ∀ (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) d)
      (c : Homology ℚ (TopCat.of (ComplexPoint X)) d)
      (hc : ∀ x, localOrientation _ _ c x = o.generator x),
    Function.Bijective ((HodgeLean.Foundations.Singular.cup
      (TopCat.of (ComplexPoint X)) hd).compr₂ (orientationIntegral _ _ c)) := by
  subst d
  exact g32n_projective_cup_perfect X n hn

/-- The middle pairing with the native degree convention. -/
theorem g32n_projective_middle_perfect
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < 2 * k)
    (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * (2 * k)))
    (c : Homology ℚ (TopCat.of (ComplexPoint X)) (2 * (2 * k)))
    (hc : ∀ x, localOrientation _ _ c x = o.generator x) :
    Function.Bijective (s2e_middlePairing (TopCat.of (ComplexPoint X)) k
      (orientationIntegral _ _ c)) := by
  exact g32n_projective_cup_perfect_degree X (2 * k) (2 * (2 * k)) hk
    (by omega) o c hc

end HodgeLean.Foundations.Program
