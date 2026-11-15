import HodgeLean.Foundations.BundleThom.RelativeSubcomplexProjectionHelpers
import HodgeLean.Foundations.BundleThom.DirectedGeneratorCoverHelpers

/-! # Scalar coverage of actual relative chains in directed subcomplex unions

The quotient retains the fixed relative subcomplex while every generator factors through a supplied domain.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology Simplicial
namespace HodgeLean.Foundations.BundleThom

/-- Directed ambient subcomplexes covering the actual n-simplices cover scalar maps to relative n-chains.
Source: Hatcher, Algebraic Topology, §2.1, finite support and relative chain quotients. -/
theorem i1_directedRelativeChain_scalar_factor {ι : Type} [Nonempty ι]
    (X : SSet) (Z : X.Subcomplex) (U : ι → X.Subcomplex) (hdir : Directed (· ≤ ·) U)
    (n : ℕ) (hcover : ∀ σ : X _⦋n⦌, ∃ i, σ ∈ (U i).obj (Opposite.op ⦋n⦌))
    (f : ModuleCat.of ℚ ℚ ⟶ ((i1_relativeSubcomplexChainFunctor X Z).obj ⊤).X n) :
    ∃ i, ∃ g : ModuleCat.of ℚ ℚ ⟶ ((i1_relativeSubcomplexChainFunctor X Z).obj (U i)).X n,
      g ≫ ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE (le_top : U i ≤ ⊤))).f n = f := by
  let F := i1_relativeSubcomplexChainFunctor X Z
  let p : ∀ i, F.obj (U i) ⟶ F.obj ⊤ := fun i => F.map (homOfLE le_top)
  have hrange (i j : ι) (hij : U i ≤ U j) :
      LinearMap.range ((p i).f n).hom ≤ LinearMap.range ((p j).f n).hom := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(F.map (homOfLE hij)).f n x, ?_⟩
    have h : F.map (homOfLE hij) ≫ p j = p i := by
      dsimp [p]
      rw [← F.map_comp]
      rfl
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom h n) x
  have hd : Directed (· ≤ ·) (fun i => LinearMap.range ((p i).f n).hom) := by
    intro i j
    obtain ⟨t, hi, hj⟩ := hdir i j
    exact ⟨t, hrange i t hi, hrange j t hj⟩
  let T : X.Subcomplex := ⊤
  let π := i1_relativeSubcomplexProjection X Z T
  haveI : Epi (π.f n) := by
    dsimp [π, i1_relativeSubcomplexProjection]
    infer_instance
  apply i1_scalarMap_factor_of_directed_generator_cover
    ((F.obj ⊤).X n) (fun i => (F.obj (U i)).X n) (fun i => (p i).f n) hd
    (fun σ : (T : SSet) _⦋n⦌ => (T : SSet).ιChainComplex σ ≫ π.f n) ?_ ?_ f
  · intro M a b hab
    apply (cancel_epi (π.f n)).mp
    apply (T : SSet).chainComplex_hom_ext
    intro σ
    simpa only [← Category.assoc] using hab σ
  · intro σ
    obtain ⟨i, hi⟩ := hcover σ.1
    let τ : (U i : SSet) _⦋n⦌ := ⟨σ.1, hi⟩
    refine ⟨i, (U i : SSet).ιChainComplex τ ≫
      (i1_relativeSubcomplexProjection X Z (U i)).f n, ?_⟩
    have hπ := HomologicalComplex.congr_hom
      (i1_relativeSubcomplexProjection_naturality X Z (U i) T le_top) n
    change (i1_relativeSubcomplexProjection X Z (U i)).f n ≫ (p i).f n =
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_top : U i ≤ T))
        (ModuleCat.of ℚ ℚ)).f n ≫ π.f n at hπ
    change (U i : SSet).ιChainComplex τ ≫
        ((i1_relativeSubcomplexProjection X Z (U i)).f n ≫ (p i).f n) = _
    rw [hπ, ← Category.assoc]
    rw [SSet.ι_chainComplexMap_f]
    rfl

end HodgeLean.Foundations.BundleThom
