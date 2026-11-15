import HodgeLean.Foundations.BundleThom.HomologyZeroDetectionHelpers

/-! # Degree-zero detection by actual covering maps

A jointly surjective family detects the vertex generators and hence degree-zero coclasses.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology.Singular Simplicial
namespace HodgeLean.Foundations.BundleThom

/-- Jointly surjective continuous maps detect linear maps out of degree-zero singular homology.
Source: Hatcher, Algebraic Topology, §2.1, degree-zero vertex generators. -/
theorem i1_homologyZero_hom_ext_of_cover {X : TopCat} {ι : Type} (Y : ι → TopCat)
    (p : ∀ i, Y i ⟶ X) (hcover : ∀ x : X, ∃ i y, p i y = x)
    {M : ModuleCat ℚ} (f g : Homology ℚ X 0 ⟶ M)
    (h : ∀ i, HomologicalComplex.homologyMap (singularChainComplexMap ℚ (p i)) 0 ≫ f =
      HomologicalComplex.homologyMap (singularChainComplexMap ℚ (p i)) 0 ≫ g) : f = g := by
  apply i1_homologyZero_hom_ext X f g
  intro σ
  obtain ⟨i, y, hy⟩ := hcover (TopCat.toSSetObj₀Equiv σ)
  let τ : (TopCat.toSSet.obj (Y i)) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm y
  have hσ : (TopCat.toSSet.map (p i)).app _ τ = σ := by
    apply TopCat.toSSetObj₀Equiv.injective
    change p i (TopCat.toSSetObj₀Equiv τ) = TopCat.toSSetObj₀Equiv σ
    simpa only [τ, Equiv.apply_symm_apply] using hy
  rw [← hσ, ← i1_vertexHomologyMap_naturality]
  rw [Category.assoc, h i, ← Category.assoc]

/-- Degree-zero rational coclasses are detected by pullback along jointly surjective continuous maps.
Source: Hatcher, Algebraic Topology, §3.1, universal coefficients in degree zero. -/
theorem i1_cohomologyZero_ext_of_cover {X : TopCat} {ι : Type} (Y : ι → TopCat)
    (p : ∀ i, Y i ⟶ X) (hcover : ∀ x : X, ∃ i y, p i y = x)
    (u v : Cohomology ℚ X 0)
    (h : ∀ i, cohomologyMap ℚ 0 (p i) u = cohomologyMap ℚ 0 (p i) v) : u = v := by
  apply (cohomologyEquivDualHomology ℚ X 0).injective
  have he := i1_homologyZero_hom_ext_of_cover Y p hcover
    (ModuleCat.ofHom (cohomologyEquivDualHomology ℚ X 0 u))
    (ModuleCat.ofHom (cohomologyEquivDualHomology ℚ X 0 v)) (by
      intro i
      apply ModuleCat.hom_ext
      ext z
      change cohomologyEquivDualHomology ℚ X 0 u (homologyMap ℚ 0 (p i) z) =
        cohomologyEquivDualHomology ℚ X 0 v (homologyMap ℚ 0 (p i) z)
      have hz := congrArg (fun c => cohomologyEquivDualHomology ℚ (Y i) 0 c z) (h i)
      simpa only [cohomologyEquivDualHomology_cohomologyMap] using hz)
  exact congrArg ModuleCat.Hom.hom he

end HodgeLean.Foundations.BundleThom
