import HodgeLean.Foundations.BundleResolution.ChernRelativeCupClassHelpers
import HodgeLean.Foundations.BundleResolution.ChernCocyclePairingHelpers

/-! # Relative cup product on actual cocycle representatives

The cohomology operation defined by cap duality is represented by the
actual relative Alexander–Whitney cup cochain.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory HomologicalComplex AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

variable (P : TopPair) (p q : ℕ)

def i1_relativeCupCocycle (φ : RelativeCocycle ℚ P p)
    (ψ : Cocycle ℚ (TopCat.toSSet.obj P.fst) q) : RelativeCocycle ℚ P (p + q) :=
  ⟨i1_relativeCupCochain P p q φ.val ψ.val,
    i1_relativeCupCochain_closed P p q φ.val ψ.val φ.property ψ.property⟩

set_option backward.isDefEq.respectTransparency false in
theorem i1_relativeCup_on_class (φ : RelativeCocycle ℚ P p)
    (ψ : Cocycle ℚ (TopCat.toSSet.obj P.fst) q) :
    i1_relativeCup P p q (i1_relativeCocycleClass P p φ)
      (cohomologyClass P.fst q ψ) =
        i1_relativeCocycleClass P (p + q) (i1_relativeCupCocycle P p q φ ψ) := by
  apply (relativeCohomologyEquivDualHomology ℚ P (p + q)).injective
  ext z
  obtain ⟨z, rfl⟩ := (((relativeChainFunctor ℚ).obj P).sc (p + q)).moduleCatHomologyClass_surjective z
  rw [i1_relativeCup_pairing_cycle, i1_cohomologyClass_pairing,
    i1_relativeCocycleClass_pairing]
  change ψ.val ((relativeCapShortComplexHom ℚ P p q φ.val φ.property).τ₂.hom z.val) =
    ψ.val (relativeCap ℚ P p q φ.val z.val)
  rw [relativeCapShortComplexHom_τ₂]
  rfl

end HodgeLean.Foundations.BundleResolution
