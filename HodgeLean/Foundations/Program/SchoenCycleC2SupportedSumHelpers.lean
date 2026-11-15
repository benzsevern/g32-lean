import HodgeLean.Foundations.AlgebraicTopology.Singular.CohomologyWithSupport
import HodgeLean.Foundations.Program.SchoenCycleC2OrbitSupportHelpers
import HodgeLean.Foundations.Program.CompensationAssemblyRelativeProduct

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Enlarging a support preserves the absolute class. -/
theorem s2e_enlargeSupport_absolute (X : TopCat.{0}) {S T : Set X}
    (hST : S ⊆ T) (n : ℕ) (c : CohomologyWithSupport ℚ X S n) :
    forgetSupport ℚ X T n (enlargeSupport ℚ X hST n c) =
      forgetSupport ℚ X S n c := by
  exact SupportedClasses.forget_enlarge X hST n c

/-- The weighted supported class omits exactly the zero coefficients. -/
def s2e_weightedSupportedClass
    (X : TopCat.{0}) (m n : ℕ) (S : Fin m → Set X) (T : Set X)
    (a : Fin m → ℚ) (hST : ∀ t, a t ≠ 0 → S t ⊆ T)
    (c : ∀ t, CohomologyWithSupport ℚ X (S t) n) : CohomologyWithSupport ℚ X T n := by
  exact SupportedClasses.weightedSum X n S T a hST c

/-- Forgetting the explicit weighted supported class gives the weighted absolute sum. -/
theorem s2e_weightedSupportedClass_absolute
    (X : TopCat.{0}) (m n : ℕ) (S : Fin m → Set X) (T : Set X)
    (a : Fin m → ℚ) (hST : ∀ t, a t ≠ 0 → S t ⊆ T)
    (c : ∀ t, CohomologyWithSupport ℚ X (S t) n) :
    forgetSupport ℚ X T n (s2e_weightedSupportedClass X m n S T a hST c) =
      ∑ t : Fin m, a t • forgetSupport ℚ X (S t) n (c t) := by
  exact SupportedClasses.forget_weightedSum X n S T a hST c

/-- Weighted classes can be placed on the union of the supports with nonzero weight. -/
theorem s2e_supported_weighted_sum
    (X : TopCat.{0}) (m n : ℕ) (S : Fin m → Set X) (T : Set X)
    (a : Fin m → ℚ) (hST : ∀ t, a t ≠ 0 → S t ⊆ T)
    (c : ∀ t, CohomologyWithSupport ℚ X (S t) n) :
    ∃ b : CohomologyWithSupport ℚ X T n,
      forgetSupport ℚ X T n b = ∑ t : Fin m, a t • forgetSupport ℚ X (S t) n (c t) :=
  ⟨s2e_weightedSupportedClass X m n S T a hST c,
    s2e_weightedSupportedClass_absolute X m n S T a hST c⟩

/-- Actual orbit component representatives give a supported rational weighted sum
on the support of the actual weighted cycle, with the prescribed absolute class. -/
theorem s2e_rationalOrbitCycle_supported_sum
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (δ : W ⟶ W) (k m : ℕ)
    (hi : Function.Injective (fun t : Fin m =>
      (ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left)))
    (himm : ∀ t : Fin m, IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom).left)
    (c : ∀ t : Fin m,
      s2e_supportedClass W (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) k)
    (a : Fin m → ℚ) :
    ∃ b : s2e_supportedClass W (s2e_rationalOrbitCycle ι δ m a) k,
      s2e_classToAbsolute W (s2e_rationalOrbitCycle ι δ m a) k b =
        ∑ t : Fin m, a t • s2e_classToAbsolute W
          (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) k (c t) := by
  apply s2e_supported_weighted_sum (TopCat.of (ComplexPoint W)) m (2 * k)
    (fun t => a3b4_cycleSupport W.hom
      (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ))
    (a3b4_cycleSupport W.hom (s2e_rationalOrbitCycle ι δ m a)) a ?_ c
  intro t ha x hx
  let : IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom).left := himm t
  rw [s2e_componentCycle_analytic_support] at hx
  rw [s2e_rationalOrbitCycle_analytic_support_eq ι δ m hi himm a]
  exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ha, hx⟩⟩

end HodgeLean.Foundations.Program
