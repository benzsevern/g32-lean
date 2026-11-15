import HodgeLean.Foundations.BundleThom.RationalChainCoclassGluingHelpers

/-! # Pullbacks of rational dual chain coclasses

The maps are induced by the actual dual cochain maps and retain composition and signs.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.BundleThom

/-- Pullback on rational dual coclasses induced by an actual chain map.
Source: Hatcher, Algebraic Topology, §3.1, rational cohomology pullbacks. -/
def i1_chainDualPullback {K L : ChainComplex (ModuleCat ℚ) ℕ} (n : ℕ) (f : K ⟶ L) :
    L.linearDualCochainComplex.homology n →ₗ[ℚ] K.linearDualCochainComplex.homology n :=
  (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap f) n).hom

/-- Actual rational dual coclass pullbacks reverse composition of chain maps.
Source: Hatcher, Algebraic Topology, §3.1, functoriality of cohomology. -/
theorem i1_chainDualPullback_comp {K L M : ChainComplex (ModuleCat ℚ) ℕ}
    (n : ℕ) (f : K ⟶ L) (g : L ⟶ M) :
    i1_chainDualPullback n (f ≫ g) = (i1_chainDualPullback n f).comp (i1_chainDualPullback n g) := by
  unfold i1_chainDualPullback
  rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

/-- The actual identity chain map induces the identity coclass pullback.
Source: Hatcher, Algebraic Topology, §3.1, functoriality of cohomology. -/
theorem i1_chainDualPullback_id (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    i1_chainDualPullback n (𝟙 K) = LinearMap.id := by
  unfold i1_chainDualPullback
  rw [HomologicalComplex.linearDualMap_id, HomologicalComplex.homologyMap_id]
  rfl

/-- Pullback of an actual rational dual coclass pairs naturally with homology pushforward.
Source: Hatcher, Algebraic Topology, §3.1, universal coefficient naturality. -/
theorem i1_chainDualPullback_pairing {K L : ChainComplex (ModuleCat ℚ) ℕ}
    (n : ℕ) (f : K ⟶ L) (u : L.linearDualCochainComplex.homology n) (z : K.homology n) :
    K.linearDualHomologyEquiv n (i1_chainDualPullback n f u) z =
      L.linearDualHomologyEquiv n u (HomologicalComplex.homologyMap f n z) :=
  HomologicalComplex.linearDualHomologyEquiv_naturality f n u z

/-- Negating an actual chain map negates its rational coclass pullback.
Source: Hatcher, Algebraic Topology, §3.1, linearity of cohomology pullbacks. -/
theorem i1_chainDualPullback_neg {K L : ChainComplex (ModuleCat ℚ) ℕ} (n : ℕ) (f : K ⟶ L) :
    i1_chainDualPullback n (-f) = -i1_chainDualPullback n f := by
  have hn : HomologicalComplex.homologyMap (-f) n = -HomologicalComplex.homologyMap f n :=
    (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map_neg
  apply LinearMap.ext
  intro u
  apply (K.linearDualHomologyEquiv n).injective
  ext z
  change K.linearDualHomologyEquiv n (i1_chainDualPullback n (-f) u) z =
    K.linearDualHomologyEquiv n (-(i1_chainDualPullback n f u)) z
  rw [map_neg]
  change K.linearDualHomologyEquiv n (i1_chainDualPullback n (-f) u) z =
    -(K.linearDualHomologyEquiv n (i1_chainDualPullback n f u) z)
  rw [i1_chainDualPullback_pairing, i1_chainDualPullback_pairing, hn]
  exact map_neg _ _

/-- The actual zero chain map induces the zero coclass pullback.
Source: Hatcher, Algebraic Topology, §3.1, linearity of cohomology pullbacks. -/
theorem i1_chainDualPullback_zero (K L : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    i1_chainDualPullback n (0 : K ⟶ L) = 0 := by
  have hz : HomologicalComplex.homologyMap (0 : K ⟶ L) n = 0 :=
    (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map_zero _ _
  apply LinearMap.ext
  intro u
  apply (K.linearDualHomologyEquiv n).injective
  ext z
  change K.linearDualHomologyEquiv n (i1_chainDualPullback n (0 : K ⟶ L) u) z =
    K.linearDualHomologyEquiv n 0 z
  rw [map_zero, i1_chainDualPullback_pairing, hz]
  exact map_zero _

end HodgeLean.Foundations.BundleThom
