import HodgeLean.Foundations.RationalHomologyManifold.PositiveCapTargetWindow
import HodgeLean.Foundations.RationalHomologyManifold.InitialCapTargetWindowTransport

/-! The actual supported-chain comparison with every positive cap window.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual supported-chain window maps into the original bounded cap window with the boundary quotient in initial degree and the specified adjacent signs.
Source: Hatcher, Algebraic Topology, section 3.3; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
def capTargetWindowComparison (X : TopCat.{0}) : ∀ p q : ℕ,
    (subdivisionLimitSheafComplex X).sc' (q + 2) (q + 1) q ⟶
      (capTargetComplex X (p + q + 2)).sc' p (p + 1) (p + 2)
  | 0, q => initialCapTargetWindowComparisonOfEq X (0 + q + 2) q (by omega)
  | p + 1, q => positiveCapTargetWindowComparison X (p + 1) q (by omega)

#print axioms capTargetWindowComparison
/-- The actual window comparison retains the specified middle cap-target term identification without an extra sign.
Source: Hatcher, Algebraic Topology, section 3.3; the middle cap convention.
HC no distance; AV milestone no distance.
-/
theorem capTargetWindowComparison_middle (X : TopCat.{0}) (p q : ℕ) :
    (capTargetWindowComparison X p q).τ₂ =
      (capTargetTermIso X (p + q + 2) (p + 1) (q + 1) (by omega) (by omega)).inv := by
  cases p with
  | zero => rfl
  | succ p => rfl

#print axioms capTargetWindowComparison_middle
/-- The last component of the actual window comparison retains exactly the next adjacent fixed-cycle sign.
Source: Hatcher, Algebraic Topology, section 3.3; the adjacent cap differential sign.
HC no distance; AV milestone no distance.
-/
theorem capTargetWindowComparison_last (X : TopCat.{0}) (p q : ℕ) :
    (capTargetWindowComparison X p q).τ₃ =
      (-1 : ℤ) ^ (p + 2) •
        (capTargetTermIso X (p + q + 2) (p + 2) q (by omega) (by omega)).inv := by
  cases p with
  | zero =>
      simp only [Nat.reduceAdd,
        (Even.add_self 1).neg_one_pow, one_smul]
      rfl
  | succ p => rfl

#print axioms capTargetWindowComparison_last
end HodgeLean.Foundations.RationalHomologyManifold
