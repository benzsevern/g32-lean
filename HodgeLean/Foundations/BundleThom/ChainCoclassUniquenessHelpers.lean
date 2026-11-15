import HodgeLean.Foundations.BundleThom.ChainDualPullbackHelpers

/-! # Detection of actual rational coclasses from homology epimorphisms

For a short exact chain sequence, lower-degree homology vanishing supplies the required epimorphism.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace HodgeLean.Foundations.BundleThom

/-- An actual chain map surjective on homology detects rational dual coclasses by pullback.
Source: Hatcher, Algebraic Topology, §3.1, universal coefficients and coclass detection. -/
theorem i1_chainDualPullback_injective_of_epi_homology
    {K L : ChainComplex (ModuleCat ℚ) ℕ} (n : ℕ) (f : K ⟶ L)
    [Epi (HomologicalComplex.homologyMap f n)] : Function.Injective (i1_chainDualPullback n f) := by
  intro u v huv
  apply (L.linearDualHomologyEquiv n).injective
  ext z
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective (HomologicalComplex.homologyMap f n)).mp
    inferInstance z
  have h := congrArg (fun a => K.linearDualHomologyEquiv n a w) huv
  simpa only [i1_chainDualPullback_pairing, hw] using h

/-- In an actual short exact chain sequence, lower intersection homology vanishing gives detection by the union pullback.
Source: Hatcher, Algebraic Topology, §3.1, Mayer–Vietoris uniqueness. -/
theorem i1_chainDualPullback_shortExact_injective
    (S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)) (hS : S.ShortExact) (n : ℕ)
    (hzero : IsZero (S.X₁.homology n)) : Function.Injective (i1_chainDualPullback (n + 1) S.g) := by
  have he := hS.homology_exact₃ (n + 1) n (by rfl)
  haveI : Epi (HomologicalComplex.homologyMap S.g (n + 1)) :=
    he.epi_f (hzero.eq_zero_of_tgt _)
  exact i1_chainDualPullback_injective_of_epi_homology (n + 1) S.g

end HodgeLean.Foundations.BundleThom
