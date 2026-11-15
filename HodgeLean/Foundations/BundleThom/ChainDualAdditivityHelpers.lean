import HodgeLean.Foundations.BundleThom.ChainDualPullbackHelpers

/-! # Additivity of actual chain coclass pullbacks -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory
namespace HodgeLean.Foundations.BundleThom

/-- Adding actual chain maps adds their induced rational coclass pullbacks.
Source: Hatcher, Algebraic Topology, §3.1, additivity of rational cohomology. -/
theorem i1_chainDualPullback_add {K L : ChainComplex (ModuleCat ℚ) ℕ}
    (n : ℕ) (f g : K ⟶ L) :
    i1_chainDualPullback n (f + g) = i1_chainDualPullback n f + i1_chainDualPullback n g := by
  have ha : HomologicalComplex.homologyMap (f + g) n =
      HomologicalComplex.homologyMap f n + HomologicalComplex.homologyMap g n :=
    (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map_add
  apply LinearMap.ext
  intro u
  apply (K.linearDualHomologyEquiv n).injective
  ext z
  change K.linearDualHomologyEquiv n (i1_chainDualPullback n (f + g) u) z =
    K.linearDualHomologyEquiv n (i1_chainDualPullback n f u + i1_chainDualPullback n g u) z
  rw [map_add]
  change K.linearDualHomologyEquiv n (i1_chainDualPullback n (f + g) u) z =
    K.linearDualHomologyEquiv n (i1_chainDualPullback n f u) z +
      K.linearDualHomologyEquiv n (i1_chainDualPullback n g u) z
  rw [i1_chainDualPullback_pairing, i1_chainDualPullback_pairing,
    i1_chainDualPullback_pairing, ha]
  exact map_add _ _ _

end HodgeLean.Foundations.BundleThom
