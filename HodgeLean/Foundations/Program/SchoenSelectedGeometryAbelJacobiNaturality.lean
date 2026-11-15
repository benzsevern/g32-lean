import HodgeLean.Foundations.Program.SchoenSelectedGeometryAbelJacobiBasepoint
import HodgeLean.Foundations.Program.SchoenSelectedGeometryTranslationBetti

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Rational Abel–Jacobi comparison is natural for holomorphic maps, with arbitrary basepoints. -/
theorem s0_abelJacobi_betti_naturality
    {C Y : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (g : b3_periodLattice ℂ C →+ b3_periodLattice ℂ Y)
    (hg : b3_IsPushforward ℂ ℂ f g)
    (hgF : b3_periodF ℂ C ≤ (b3_periodF ℂ Y).comap (b2_cplxMap g))
    (p₀ : C) (p₁ : Y) (aj : C → b3_Jacobian ℂ C) (aj' : Y → b3_Jacobian ℂ Y)
    (haj : b3_IsAbelJacobi ℂ C p₀ aj) (haj' : b3_IsAbelJacobi ℂ Y p₁ aj')
    (hc : Continuous aj) (hc' : Continuous aj') :
    (cohomologyMap ℚ 1 (TopCat.ofHom ⟨aj, hc⟩)).comp
        (cohomologyMap ℚ 1 (TopCat.ofHom ⟨b2_torusHom _ _ g hgF,
          b2t_torusHom_continuous _ _ g hgF⟩)) =
      (cohomologyMap ℚ 1 (TopCat.ofHom ⟨f, hf.continuous⟩)).comp
        (cohomologyMap ℚ 1 (TopCat.ofHom ⟨aj', hc'⟩)) := by
  letI := b3_periodLattice_finite (C := Y) (Module.finrank_self ℂ)
  letI := b3_periodLattice_free (E := ℂ) (C := Y)
  obtain ⟨e, _⟩ := b2_torus_addEquiv (Module.finBasis ℤ (b3_periodLattice ℂ Y))
    (b3_periodF ℂ Y) (b3_isWeightOne (Module.finrank_self ℂ))
  letI : PathConnectedSpace (b3_Jacobian ℂ Y) := e.toHomeomorph.symm.pathConnectedSpace
  let φ : TopCat.of (b3_Jacobian ℂ C) ⟶ TopCat.of (b3_Jacobian ℂ Y) :=
    TopCat.ofHom ⟨b2_torusHom _ _ g hgF, b2t_torusHom_continuous _ _ g hgF⟩
  let τ : TopCat.of (b3_Jacobian ℂ Y) ⟶ TopCat.of (b3_Jacobian ℂ Y) :=
    TopCat.ofHom ⟨fun x ↦ x + aj' (f p₀), continuous_id.add continuous_const⟩
  have hm : TopCat.ofHom ⟨aj, hc⟩ ≫ φ ≫ τ =
      TopCat.ofHom ⟨f, hf.continuous⟩ ≫ TopCat.ofHom ⟨aj', hc'⟩ := by
    ext x : 1
    have hn := b3_abelJacobi_natural (Module.finrank_self ℂ) (Module.finrank_self ℂ)
      f hf g hg hgF p₀ aj haj (fun y ↦ aj' y - aj' (f p₀))
      (s0_abelJacobi_rebase p₁ (f p₀) aj' haj') x
    exact (sub_eq_iff_eq_add.mp hn).symm
  have ht : cohomologyMap ℚ 1 τ = LinearMap.id := s0_translation_pullback _ _ 1
  have h := congrArg (fun m ↦ cohomologyMap ℚ 1 m) hm
  simpa only [cohomologyMap_comp, ht, LinearMap.comp_id] using h

#print axioms s0_abelJacobi_betti_naturality
end HodgeLean.Foundations.Program
