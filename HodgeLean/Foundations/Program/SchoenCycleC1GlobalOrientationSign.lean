import HodgeLean.Foundations.Program.SchoenCycleC1IntegralFundamentalClass
import HodgeLean.Foundations.Program.SchoenCycleC1FundamentalClassNaturality
import HodgeLean.Foundations.Program.SchoenTowerL1bActionLocalSign

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- An actual homeomorphism between connected compact complex curves has
one integral orientation sign at every point, obtained from its action on
the global fundamental generators rather than separately selected signs. -/
theorem s2e_c1_homeomorphism_global_orientation_sign
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [T2Space N] [CompactSpace N] [ConnectedSpace N]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) 1 M]
    [ChartedSpace (Fin 1 → ℂ) N] [IsManifold 𝓘(ℂ, Fin 1 → ℂ) 1 N]
    (E : M ≃ₜ N) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ x : M,
      relativeHomologyMap ℤ 2
        (imagePointPairMap (TopCat.ofHom ⟨E, E.continuous⟩) E.injective x)
        (b6m_surfaceLocalClass ℤ x) = ε • b6m_manifoldLocalClass ℤ 1 (E x) := by
  obtain ⟨wM, hwM, hgenM⟩ := b6m_surface_fundamental_generator ℤ (C := M)
  obtain ⟨wN, hwN, hgenN⟩ := s2e_c1_manifold_one_fundamental_generator N
  let F : TopCat.{0} ⥤ ModuleCat.{0} ℤ :=
    (singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)
  let e : TopCat.of M ≅ TopCat.of N := TopCat.isoOfHomeo E
  have hb : Function.Bijective (homologyMap ℤ 2 e.hom) :=
    (ConcreteCategory.isIso_iff_bijective (F.map e.hom)).mp inferInstance
  have hsrc : Function.Surjective (fun r : ℤ => r • wM) := by
    convert hgenM.2 using 1
    funext r
    exact (Int.cast_smul_eq_zsmul ℤ r wM).symm
  obtain ⟨ε, hε, he⟩ := s2v_l1b_action_integer_generator_sign
    (homologyMap ℤ 2 e.hom) hb.2 wM wN hsrc hgenN
  refine ⟨ε, hε, fun x => ?_⟩
  have hn := s2e_c1_relative_homology_projection_naturality ℤ
    (imagePointPairMap (TopCat.ofHom ⟨E, E.continuous⟩) E.injective x) 2 wM
  rw [hwM x] at hn
  change relativeHomologyMap ℤ 2
      (imagePointPairMap (TopCat.ofHom ⟨E, E.continuous⟩) E.injective x)
      (b6m_surfaceLocalClass ℤ x) =
    (relativeHomologyProjection ℤ (pointComplementPair (E x)) 2).hom
      (homologyMap ℤ 2 e.hom wM) at hn
  rw [he, map_zsmul, hwN] at hn
  exact hn

end HodgeLean.Foundations.Program
