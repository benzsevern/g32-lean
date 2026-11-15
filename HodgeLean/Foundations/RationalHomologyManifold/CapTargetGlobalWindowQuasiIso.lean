import HodgeLean.Foundations.RationalHomologyManifold.CapTargetWindowComparison
import HodgeLean.Foundations.RationalHomologyManifold.InitialGlobalCapWindowEpi

/-! Actual global supported-chain windows and bounded cap windows have the same homology.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual signed window comparison is a quasi-isomorphism on global sections, including its initial top boundary quotient.
Source: Bredon, Sheaf Theory, second edition, II.9 and VI.12; the actual global boundary quotient and the cap grading.
HC no distance; AV milestone no distance.
-/
theorem capTargetWindowComparison_global_quasiIso (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (p q : ℕ) (o : LocalRationalOrientation X (p + q + 2)) :
    ShortComplex.QuasiIso (((subdivisionGlobalSectionsFunctor X).mapShortComplex).map
      (capTargetWindowComparison X p q)) := by
  let E := subdivisionGlobalSectionsFunctor X
  let γ := capTargetWindowComparison X p q
  let φ := E.mapShortComplex.map γ
  letI : IsIso φ.τ₂ := by
    change IsIso (E.map γ.τ₂)
    dsimp only [γ]
    rw [capTargetWindowComparison_middle]
    infer_instance
  letI : Mono φ.τ₃ := by
    haveI : IsIso γ.τ₃ := by
      dsimp only [γ]
      rw [capTargetWindowComparison_last]
      change IsIso ((((-1 : ℤˣ) ^ (p + 2)) •
        (capTargetTermIso X (p + q + 2) (p + 2) q (by omega) (by omega)).symm).hom)
      infer_instance
    change Mono (E.map γ.τ₃)
    infer_instance
  letI : Epi φ.τ₁ := by
    cases p with
    | zero =>
        change Epi (E.map (initialCapTargetWindowComparisonOfEq X (0 + q + 2) q (by omega)).τ₁)
        exact initialCapTargetWindowComparisonOfEq_global_epi X t (0 + q + 2) q (by omega) o
    | succ p =>
        haveI : IsIso (capTargetWindowComparison X (p + 1) q).τ₁ := by
          change IsIso ((-1 : ℤ) ^ (p + 1 + 1) •
            (capTargetTermIso X (p + 1 + q + 2) (p + 1) (q + 2) (by omega) (by omega)).inv)
          change IsIso ((((-1 : ℤˣ) ^ (p + 1 + 1)) •
            (capTargetTermIso X (p + 1 + q + 2) (p + 1) (q + 2) (by omega) (by omega)).symm).hom)
          infer_instance
        change Epi (E.map (capTargetWindowComparison X (p + 1) q).τ₁)
        infer_instance
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

#print axioms capTargetWindowComparison_global_quasiIso
end HodgeLean.Foundations.RationalHomologyManifold
