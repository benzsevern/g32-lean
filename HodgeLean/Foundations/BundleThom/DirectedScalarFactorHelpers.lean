import HodgeLean.Foundations.BundleThom.ChainCoverHomologyLiftingHelpers

/-! # Scalar-map factorization through directed rational ranges

A scalar map is determined by its value at one, which lies in one of the directed ranges.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.BundleThom

/-- Directed rational linear ranges spanning the target cover every map from the scalar module.
Source: Hatcher, Algebraic Topology, §2.1, finite support in directed chain unions. -/
theorem i1_scalarMap_factor_of_directed_ranges {ι : Type} [Nonempty ι]
    (V : ModuleCat ℚ) (L : ι → ModuleCat ℚ) (p : ∀ i, L i ⟶ V)
    (hdir : Directed (· ≤ ·) (fun i => LinearMap.range (p i).hom))
    (hsup : (⨆ i, LinearMap.range (p i).hom) = ⊤)
    (f : ModuleCat.of ℚ ℚ ⟶ V) :
    ∃ i, ∃ g : ModuleCat.of ℚ ℚ ⟶ L i, g ≫ p i = f := by
  have hx : f 1 ∈ ⨆ i, LinearMap.range (p i).hom := by
    rw [hsup]
    trivial
  obtain ⟨i, x, hx⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hx
  refine ⟨i, ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ (L i) x), ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change p i ((1 : ℚ) • x) = f 1
  simpa only [one_smul] using hx

end HodgeLean.Foundations.BundleThom
