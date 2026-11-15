import HodgeLean.Foundations.BundleResolution.ChernRelativeCupCocycleHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeForgetClassHelpers
import HodgeLean.Foundations.BundleResolution.ChernCupRepresentativeHelpers

/-! # Relative cup multiplication after forgetting support

Forgetting support intertwines the actual relative cup action with the
ordinary singular cup product.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

variable (P : TopPair) (p q : ℕ)

theorem i1_relativeCup_toAbsolute (α : RelativeCohomology ℚ P p)
    (β : Cohomology ℚ P.fst q) :
    relativeCohomologyToAbsolute ℚ P (p + q) (i1_relativeCup P p q α β) =
      cup P.fst rfl (relativeCohomologyToAbsolute ℚ P p α) β := by
  obtain ⟨φ, rfl⟩ := i1_relativeCocycleClass_surjective P p α
  obtain ⟨ψ, rfl⟩ := cohomologyClass_surjective P.fst q β
  rw [i1_relativeCup_on_class, i1_relativeCocycleClass_toAbsolute,
    i1_relativeCocycleClass_toAbsolute, i1_cup_on_class]
  apply congrArg (cohomologyClass P.fst (p + q))
  apply Subtype.ext
  exact i1_relativeCupCochain_toAbsolute P p q φ.val ψ.val

theorem i1_relativeCup_one (α : RelativeCohomology ℚ P p) :
    i1_relativeCup P p 0 α (unit P.fst) = α := by
  obtain ⟨φ, rfl⟩ := i1_relativeCocycleClass_surjective P p α
  change i1_relativeCup P p 0 (i1_relativeCocycleClass P p φ)
    (cohomologyClass P.fst 0 ⟨unitCochain P.fst, coboundary_unitCochain P.fst⟩) = _
  rw [i1_relativeCup_on_class]
  apply congrArg (i1_relativeCocycleClass P p)
  apply Subtype.ext
  exact i1_relativeCupCochain_one P p φ.val

end HodgeLean.Foundations.BundleResolution
