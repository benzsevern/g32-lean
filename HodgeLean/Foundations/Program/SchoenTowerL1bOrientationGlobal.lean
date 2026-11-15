import HodgeLean.Foundations.Program.SchoenTowerL1bActionSplitDefs
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceFundamentalClass
import HodgeLean.Foundations.Port.AlgebraicGeometry.ComplexPoint.SmoothConnected

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

theorem s2v_l1b_projection_map (R : Type) [CommRing R]
    {P Q : TopPair} (f : P ⟶ Q) (n : ℕ) (w : Homology R P.fst n) :
    relativeHomologyMap R n f ((relativeHomologyProjection R P n).hom w) =
      (relativeHomologyProjection R Q n).hom (homologyMap R n (TopPair.Hom.fst f) w) := by
  have h := TopPair.Homotopy.relativeChainProjection_naturality (R := R) f
  change (HomologicalComplex.homologyMap ((relativeChainFunctor R).map f) n).hom
    ((HomologicalComplex.homologyMap (relativeChainProjection R P) n).hom w) = _
  rw [b6m_homologyMap_hom_comp_apply, h]
  rw [← b6m_homologyMap_hom_comp_apply]
  rfl

theorem s2v_l1b_native_generator (R : Type) [CommRing R] (d : ℕ) (hd : d = 1)
    {N : Type} [TopologicalSpace N] [T2Space N] [CompactSpace N]
    [ConnectedSpace N] [ChartedSpace (Fin d → ℂ) N]
    [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 N] :
    ∃ w : Homology R (TopCat.of N) 2,
      (∀ x : N, (relativeHomologyProjection R (pointComplementPair x) 2).hom w =
        (show RelativeHomology R (pointComplementPair x) 2 from by
          simpa only [hd, mul_one] using b6m_manifoldLocalClass R d x)) ∧
      Function.Bijective (fun r : R => r • w) := by
  subst d
  let P := TopPair.ofSubset (X := TopCat.of N)
    (((⊤ : TopologicalSpace.Opens N) : Set N)ᶜ)
  haveI : IsEmpty P.snd := by
    change IsEmpty ↥(((⊤ : TopologicalSpace.Opens N) : Set N)ᶜ)
    rw [TopologicalSpace.Opens.coe_top, Set.compl_univ]
    infer_instance
  obtain ⟨v, hv⟩ := b6m_manifold_globalOrientation R 1 (M := N)
  obtain ⟨w, hw⟩ := (b6m_relativeHomologyProjection_bijective_of_isEmpty R P 2).2 v
  have hwlocal : ∀ x : N,
      (relativeHomologyProjection R (pointComplementPair x) 2).hom w =
        b6m_manifoldLocalClass R 1 x := by
    intro x
    have h := b6m_relativeHomologyProjection_support R (TopCat.of N)
      (Set.singleton_subset_iff.mpr (TopologicalSpace.Opens.mem_top x)) 2 w
    rw [hw] at h
    exact h.symm.trans (hv x)
  refine ⟨w, hwlocal, b6m_absolute_topHomology_generated_by_point_generators R
    (E := Fin 1 → ℂ) (by simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]) w ?_⟩
  intro x
  rw [hwlocal]
  exact b6m_localClassOfChart_one_smul_bijective R _ x (mem_chart_source _ x)

theorem s2v_l1b_native_local_generator (R : Type) [CommRing R]
    (d : ℕ) (hd : d = 1) {N : Type} [TopologicalSpace N] [T1Space N]
    [ChartedSpace (Fin d → ℂ) N] (p : N) :
    Function.Bijective (fun r : R => r •
      (show RelativeHomology R (pointComplementPair p) 2 from by
        simpa only [hd, mul_one] using b6m_manifoldLocalClass R d p)) := by
  subst d
  exact b6m_localClassOfChart_one_smul_bijective R _ p (mem_chart_source _ p)

end HodgeLean.Foundations.Program
