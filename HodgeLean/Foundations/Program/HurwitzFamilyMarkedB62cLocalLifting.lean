import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cBoundaryLifting
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular

theorem b6m_contractible_homology_isZero (R : Type) [CommRing R]
    (T : Type) [TopologicalSpace T] [ContractibleSpace T] (k : ℕ) (hk : k ≠ 0) :
    IsZero (Homology R (TopCat.of T) k) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit T
  let F := (singularHomologyFunctor.{0} (ModuleCat.{0} R) k).obj (ModuleCat.of R R)
  let f : TopCat.of T ⟶ TopCat.of Unit := TopCat.ofHom e.toFun
  let g : TopCat.of Unit ⟶ TopCat.of T := TopCat.ofHom e.invFun
  let i : F.obj (TopCat.of T) ≅ F.obj (TopCat.of Unit) :=
    Iso.mk (F.map f) (F.map g) (by
      rw [← F.map_comp, ← F.map_id]
      exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
        e.left_inv.some (ModuleCat.of R R) k) (by
      rw [← F.map_comp, ← F.map_id]
      exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
        e.right_inv.some (ModuleCat.of R R) k)
  exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat R) k (ModuleCat.of R R) (TopCat.of Unit) hk).of_iso i

theorem b6m_exact_complex_cycle_lifting (R : Type) [CommRing R] [IsDomain R]
    (S : ShortComplex (ModuleCat.{0} R)) [Module.IsTorsionFree R S.X₃]
    (hS : S.Exact) (n : R) (hn : n ≠ 0) (c : S.X₁) (z : S.X₂)
    (hc : S.f.hom c = n • z) :
    ∃ w q : S.X₁, S.f.hom w = 0 ∧ c - w = n • q := by
  have hz : S.g.hom z = 0 := by
    apply (smul_eq_zero.mp (show n • S.g.hom z = 0 from ?_)).resolve_left hn
    rw [← map_smul, ← hc]
    exact S.moduleCat_zero_apply c
  obtain ⟨q, hq⟩ := S.moduleCat_exact_iff.mp hS z hz
  refine ⟨c - n • q, q, ?_, ?_⟩
  · rw [map_sub, map_smul, hq, hc, sub_self]
  · abel

set_option backward.isDefEq.respectTransparency false in
theorem b6m_contractible_cycle_lifting (T : Type) [TopologicalSpace T]
    [ContractibleSpace T] (n : ℤ) (hn : n ≠ 0)
    (c : (SingularChainComplex ℤ (TopCat.of T)).X 2)
    (z : (SingularChainComplex ℤ (TopCat.of T)).X 1)
    (hc : ((SingularChainComplex ℤ (TopCat.of T)).d 2 1).hom c =
      ((SingularChainComplex ℤ (TopCat.of T)).X 1).isModule.smul n z) :
    ∃ w q : (SingularChainComplex ℤ (TopCat.of T)).X 2,
      ((SingularChainComplex ℤ (TopCat.of T)).d 2 1).hom w = 0 ∧ c - w =
        ((SingularChainComplex ℤ (TopCat.of T)).X 2).isModule.smul n q := by
  let K := SingularChainComplex ℤ (TopCat.of T)
  have hK : K.ExactAt 1 :=
    (K.exactAt_iff_isZero_homology 1).mpr (b6m_contractible_homology_isZero ℤ T 1 one_ne_zero)
  have hS : (K.sc' 2 1 0).Exact :=
    (K.exactAt_iff' (i := 2) (j := 1) (k := 0) (by simp) (by simp)).mp hK
  haveI : Module.IsTorsionFree ℤ (K.sc' 2 1 0).X₃ :=
    b6m_singular_chain_torsionFree T 0
  exact b6m_exact_complex_cycle_lifting ℤ (K.sc' 2 1 0) hS n hn c z hc

theorem b6m_convex_chart_cycle_lifting {T E : Type} [TopologicalSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : OpenPartialHomeomorph T E)
    (he : Convex ℝ e.target) (hne : e.target.Nonempty) (n : ℤ) (hn : n ≠ 0)
    (c : (SingularChainComplex ℤ (TopCat.of e.source)).X 2)
    (z : (SingularChainComplex ℤ (TopCat.of e.source)).X 1)
    (hc : ((SingularChainComplex ℤ (TopCat.of e.source)).d 2 1).hom c =
      ((SingularChainComplex ℤ (TopCat.of e.source)).X 1).isModule.smul n z) :
    ∃ w q : (SingularChainComplex ℤ (TopCat.of e.source)).X 2,
      ((SingularChainComplex ℤ (TopCat.of e.source)).d 2 1).hom w = 0 ∧ c - w =
        ((SingularChainComplex ℤ (TopCat.of e.source)).X 2).isModule.smul n q := by
  haveI : ContractibleSpace e.target := he.contractibleSpace hne
  haveI : ContractibleSpace e.source := e.toHomeomorphSourceTarget.contractibleSpace
  exact b6m_contractible_cycle_lifting e.source n hn c z hc

end HodgeLean.Foundations.Program
