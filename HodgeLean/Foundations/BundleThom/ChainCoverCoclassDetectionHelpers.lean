import HodgeLean.Foundations.BundleThom.ChainCoverHomologyLiftingHelpers

/-! # Rational coclass detection by monic chain covers

Projective homology representatives turn chain-degree coverage into actual coclass detection.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.BundleThom

/-- Degreewise monic chain maps covering scalar chain generators in degree n detect rational dual coclasses in degree n.
Source: Hatcher, Algebraic Topology, §2.1 and §3.1, cycle representatives and universal coefficients. -/
theorem i1_chainCoverCoclass_ext {ι : Type}
    (K : ChainComplex (ModuleCat ℚ) ℕ) (L : ι → ChainComplex (ModuleCat ℚ) ℕ)
    (p : ∀ i, L i ⟶ K) [∀ i j, Mono ((p i).f j)] (n : ℕ)
    (hcover : ∀ f : ModuleCat.of ℚ ℚ ⟶ K.X n,
      ∃ i, ∃ g : ModuleCat.of ℚ ℚ ⟶ (L i).X n, g ≫ (p i).f n = f)
    (u v : K.linearDualCochainComplex.homology n)
    (h : ∀ i, i1_chainDualPullback n (p i) u = i1_chainDualPullback n (p i) v) : u = v := by
  apply (K.linearDualHomologyEquiv n).injective
  ext z
  let f : ModuleCat.of ℚ ℚ ⟶ K.homology n :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ (K.homology n) z)
  obtain ⟨i, g, hg⟩ := i1_chainCover_projectiveHomology_factor K L p
    (ModuleCat.of ℚ ℚ) n hcover f
  have hz : HomologicalComplex.homologyMap (p i) n (g 1) = z := by
    have he := ConcreteCategory.congr_hom hg 1
    change HomologicalComplex.homologyMap (p i) n (g 1) = (1 : ℚ) • z at he
    simpa only [one_smul] using he
  have he := congrArg (fun c => (L i).linearDualHomologyEquiv n c (g 1)) (h i)
  simpa only [i1_chainDualPullback_pairing, hz] using he

end HodgeLean.Foundations.BundleThom
