import HodgeLean.Foundations.Program.HurwitzFamilyMarkedDefs

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters

theorem b6m_homologyMap_loopCycle {C D : Type} [TopologicalSpace C] [TopologicalSpace D]
    (f : C(C, D)) (p : C(UnitAddCircle, C)) :
    homologyMap ℤ 1 (TopCat.ofHom f)
      (((SingularChainComplex ℤ (TopCat.of C)).sc 1).moduleCatHomologyClass (loopCycle ℤ p)) =
      ((SingularChainComplex ℤ (TopCat.of D)).sc 1).moduleCatHomologyClass
        (loopCycle ℤ (f.comp p)) := by
  let F := ((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map
    (TopCat.ofHom f)
  let S := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (.down ℕ) 1).map F
  change (ShortComplex.homologyMap S).hom _ = _
  rw [ShortComplex.moduleCatHomologyClass_naturality]
  congr 1
  apply Subtype.ext
  change ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
    (ModuleCat.of ℤ ℤ)).f 1).hom (Simplicial.chainOfSimplex ℤ (loopSimplex p)) =
      Simplicial.chainOfSimplex ℤ (loopSimplex (f.comp p))
  rw [Simplicial.chainOfSimplex_map]
  rfl

open scoped Manifold ContDiff

theorem b6m_integral_loopClass_homotopy {C : Type} [TopologicalSpace C]
    {p q : C(UnitAddCircle, C)} (H : ContinuousMap.Homotopy p q) :
    ((SingularChainComplex ℤ (TopCat.of C)).sc 1).moduleCatHomologyClass (loopCycle ℤ p) =
      ((SingularChainComplex ℤ (TopCat.of C)).sc 1).moduleCatHomologyClass (loopCycle ℤ q) := by
  have h : homologyMap ℤ 1 (TopCat.ofHom p) = homologyMap ℤ 1 (TopCat.ofHom q) := by
    exact congrArg ModuleCat.Hom.hom
      (TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
        (f := TopCat.ofHom p) (g := TopCat.ofHom q) H (ModuleCat.of ℤ ℤ) 1)
  have hp := b6m_homologyMap_loopCycle p (ContinuousMap.id UnitAddCircle)
  have hq := b6m_homologyMap_loopCycle q (ContinuousMap.id UnitAddCircle)
  rw [h] at hp
  exact hp.symm.trans hq

theorem b6m_H1Equiv_loopClass {C D : Type} [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    (e : C ≃ₜ D) (γ : b3_SmoothLoop ℂ C) (δ : b3_SmoothLoop ℂ D)
    (h : ∀ t : ℝ, e (γ.1 t) = δ.1 t) :
    b6m_H1Equiv e (b6m_loopClass C γ) = b6m_loopClass D δ := by
  let p : C(UnitAddCircle, C) := ⟨γ.2.1.lift, by
    rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact γ.2.2.continuous⟩
  let q : C(UnitAddCircle, D) := ⟨δ.2.1.lift, by
    rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact δ.2.2.continuous⟩
  have heq : (⟨e, e.continuous⟩ : C(C, D)).comp p = q := by
    ext t
    induction t using Quotient.inductionOn with
    | h t => exact h t
  change homologyMap ℤ 1 (TopCat.ofHom ⟨e, e.continuous⟩)
    (((SingularChainComplex ℤ (TopCat.of C)).sc 1).moduleCatHomologyClass (loopCycle ℤ p)) = _
  rw [b6m_homologyMap_loopCycle, heq]
  rfl

theorem b6m_exists_integral_smoothLoop (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (p : C(UnitAddCircle, C)) :
    ∃ γ : b3_SmoothLoop ℂ C, b6m_loopClass C γ =
      ((SingularChainComplex ℤ (TopCat.of C)).sc 1).moduleCatHomologyClass (loopCycle ℤ p) := by
  obtain ⟨γ, q, hγq, ⟨H⟩⟩ := b3Rest_exists_homotopic_smoothLoop (E := ℂ) p
  refine ⟨γ, ?_⟩
  let r : C(UnitAddCircle, C) := ⟨γ.2.1.lift, by
    rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact γ.2.2.continuous⟩
  have hr : r = q := by
    ext t
    induction t using Quotient.inductionOn with
    | h t => exact hγq t
  change ((SingularChainComplex ℤ (TopCat.of C)).sc 1).moduleCatHomologyClass
    (loopCycle ℤ r) = _
  rw [hr]
  exact (b6m_integral_loopClass_homotopy H).symm

theorem b6m_period_map_surjective (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (P : b6m_H1 C →ₗ[ℤ] b3_periodLattice ℂ C)
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ) :
    Function.Surjective P := by
  intro y
  apply b3Rest2_lattice_induction (E := ℂ) (C := C) (fun y ↦ ∃ x, P x = y)
  · exact ⟨0, map_zero P⟩
  · rintro y z ⟨x, rfl⟩ ⟨w, rfl⟩
    exact ⟨x + w, map_add P x w⟩
  · rintro y ⟨x, rfl⟩
    exact ⟨-x, map_neg P x⟩
  · intro γ
    exact ⟨b6m_loopClass C γ, hP γ⟩

end HodgeLean.Foundations.Program
