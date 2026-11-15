import HodgeLean.Foundations.BundleThom.ChainDualPullbackHelpers

/-! # Actual rational coclass transfer along chain quasi-isomorphisms

Homology isomorphisms and natural universal coefficients give the actual coclass pullback equivalence.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.BundleThom

/-- The actual rational dual coclass pullback of a chain quasi-isomorphism is bijective in every degree.
Source: Hatcher, Algebraic Topology, §3.1, universal coefficients and quasi-isomorphisms. -/
theorem i1_chainDualPullback_bijective {K L : ChainComplex (ModuleCat ℚ) ℕ}
    (n : ℕ) (f : K ⟶ L) [QuasiIso f] : Function.Bijective (i1_chainDualPullback n f) := by
  let e := (asIso (HomologicalComplex.homologyMap f n)).toLinearEquiv
  constructor
  · intro u v huv
    apply (L.linearDualHomologyEquiv n).injective
    ext z
    obtain ⟨w, rfl⟩ := e.surjective z
    change L.linearDualHomologyEquiv n u (HomologicalComplex.homologyMap f n w) =
      L.linearDualHomologyEquiv n v (HomologicalComplex.homologyMap f n w)
    rw [← i1_chainDualPullback_pairing, ← i1_chainDualPullback_pairing, huv]
  · intro a
    let φ := (K.linearDualHomologyEquiv n a).comp e.symm.toLinearMap
    let b := (L.linearDualHomologyEquiv n).symm φ
    refine ⟨b, ?_⟩
    apply (K.linearDualHomologyEquiv n).injective
    ext z
    rw [i1_chainDualPullback_pairing]
    change L.linearDualHomologyEquiv n b (e z) = K.linearDualHomologyEquiv n a z
    rw [show L.linearDualHomologyEquiv n b = φ from (L.linearDualHomologyEquiv n).apply_symm_apply φ]
    change K.linearDualHomologyEquiv n a (e.symm (e z)) = _
    rw [e.symm_apply_apply]

/-- The actual pullback equivalence on rational dual coclasses of a supplied chain quasi-isomorphism.
Source: Hatcher, Algebraic Topology, §3.1, rational coclass transfer. -/
def i1_chainDualPullbackEquiv {K L : ChainComplex (ModuleCat ℚ) ℕ}
    (n : ℕ) (f : K ⟶ L) [QuasiIso f] :
    L.linearDualCochainComplex.homology n ≃ₗ[ℚ] K.linearDualCochainComplex.homology n :=
  LinearEquiv.ofBijective (i1_chainDualPullback n f) (i1_chainDualPullback_bijective n f)

end HodgeLean.Foundations.BundleThom
