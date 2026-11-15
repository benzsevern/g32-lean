import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceChains
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CoefficientBaseChange

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory

theorem b6m_boundary_division_iff_cycle_lifting
    {R M N : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.IsTorsionFree R N] (d : M →ₗ[R] N) (n : R) (hn : n ≠ 0) :
    (∀ z : N, n • z ∈ LinearMap.range d → z ∈ LinearMap.range d) ↔
      ∀ (c : M) (z : N), d c = n • z →
        ∃ (w q : M), d w = 0 ∧ c - w = n • q := by
  constructor
  · intro h c z hc
    obtain ⟨q, hq⟩ := h z ⟨c, hc⟩
    refine ⟨c - n • q, q, ?_, ?_⟩
    · rw [map_sub, map_smul, hq, hc, sub_self]
    · abel
  · intro h z hz
    obtain ⟨c, hc⟩ := hz
    obtain ⟨w, q, hw, hq⟩ := h c z hc
    refine ⟨q, smul_right_injective N hn ?_⟩
    calc
      n • d q = d (n • q) := (d.map_smul n q).symm
      _ = d (c - w) := congrArg d hq.symm
      _ = n • z := by rw [map_sub, hw, sub_zero, hc]

set_option backward.isDefEq.respectTransparency false in
theorem b6m_homology_torsionFree_of_cycle_lifting
    (R : Type) [CommRing R] [IsDomain R] (S : ShortComplex (ModuleCat.{0} R))
    [Module.IsTorsionFree R S.X₂]
    (hlift : ∀ (n : R), n ≠ 0 → ∀ (c : S.X₁) (z : S.X₂),
      S.f.hom c = n • z → ∃ (w q : S.X₁), S.f.hom w = 0 ∧ c - w = n • q) :
    Module.IsTorsionFree R S.homology := by
  apply b6m_homology_torsionFree_of_saturated R S
  intro n hn
  exact (b6m_boundary_division_iff_cycle_lifting S.f.hom n hn).mpr (hlift n hn)

open AlgebraicTopology.Singular

theorem b6m_singular_chain_torsionFree (T : Type) [TopologicalSpace T] (n : ℕ) :
    Module.IsTorsionFree ℤ ((SingularChainComplex ℤ (TopCat.of T)).X n) := by
  let e := (chainGroupFinsuppIso ℤ (TopCat.of T) n).toLinearEquiv
  exact Function.Injective.moduleIsTorsionFree e e.injective
    (fun k x ↦ e.map_smul' k x)

open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false in
theorem b6m_period_comparison_of_integral_cycle_lifting
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hlift : ∀ (n : ℤ), n ≠ 0 →
      ∀ (c : (SingularChainComplex ℤ (TopCat.of C)).X 2)
        (z : (SingularChainComplex ℤ (TopCat.of C)).X 1),
      ((SingularChainComplex ℤ (TopCat.of C)).d 2 1).hom c =
        ((SingularChainComplex ℤ (TopCat.of C)).X 1).isModule.smul n z →
        ∃ (w q : (SingularChainComplex ℤ (TopCat.of C)).X 2),
          ((SingularChainComplex ℤ (TopCat.of C)).d 2 1).hom w = 0 ∧ c - w =
            ((SingularChainComplex ℤ (TopCat.of C)).X 2).isModule.smul n q) :
    ∃ P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C,
      ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ := by
  have liftAt (j : ℕ) (hj : j = 2) :
      ∀ (n : ℤ), n ≠ 0 →
        ∀ (c : (SingularChainComplex ℤ (TopCat.of C)).X j)
          (z : (SingularChainComplex ℤ (TopCat.of C)).X 1),
        ((SingularChainComplex ℤ (TopCat.of C)).d j 1).hom c =
        ((SingularChainComplex ℤ (TopCat.of C)).X 1).isModule.smul n z →
          ∃ (w q : (SingularChainComplex ℤ (TopCat.of C)).X j),
            ((SingularChainComplex ℤ (TopCat.of C)).d j 1).hom w = 0 ∧ c - w =
              ((SingularChainComplex ℤ (TopCat.of C)).X j).isModule.smul n q := by
    subst j
    exact hlift
  let S := (SingularChainComplex ℤ (TopCat.of C)).sc 1
  haveI : Module.IsTorsionFree ℤ S.X₂ := b6m_singular_chain_torsionFree C 1
  haveI : Module.IsTorsionFree ℤ (b6m_H1 C) :=
    b6m_homology_torsionFree_of_cycle_lifting ℤ S
      (liftAt _ (ChainComplex.prev ℕ 1))
  exact b6m_period_comparison_of_torsionFree C

end HodgeLean.Foundations.Program
