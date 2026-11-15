import HodgeLean.Foundations.IntegralHomology.StageTwo.SimplicialModel
import HodgeLean.Foundations.IntegralHomology.StageTwo.GeometricRealization
import HodgeLean.Foundations.IntegralHomology.StageTwo.IntegralEvaluation
import HodgeLean.Foundations.IntegralHomology.StageTwo.FiniteModel
import HodgeLean.Foundations.Semialgebraic.CompatibleTriangulation
import HodgeLean.Adapters.RationalSheafComparisonDefs
import HodgeLean.Foundations.IntegralHomology.Basic
import HodgeLean.Foundations.Topology.RationalSheafComparison
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-! Stage-two finite integral models and universal coefficient comparison specifications.
These assertions give implications from the displayed topology and finiteness inputs.
Integration and the period image belong to later stages.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular AlgebraicGeometry
open AlgebraicGeometry.ComplexPoint TopologicalSpace HodgeLean.RealDefs
open scoped TensorProduct
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

/-- Finite geometric triangulations supply bounded finite free chains with a singular chain homotopy comparison.
Source: Hatcher, Algebraic Topology, Theorem 2.27 and §2.2. -/
theorem triangulated_model_aux (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) :
    ∃ M : FiniteChainModel (TopCat.of K.space), ∀ j,
      M.rank j = Nat.card {s : Finset (EuclideanSpace ℝ (Fin n)) //
        s ∈ K.faces ∧ s.card = j + 1} := by
  classical
  obtain ⟨m, v, hv, hV⟩ := finite_vertex_enumeration K hK
  let P := indexedFaces K v
  let A : SSet.{0} := faceComplex P
  let e : SSet.toTop.obj A ≅ TopCat.of K.space :=
    TopCat.isoOfHomeo (indexedGeometricRealizationHomeomorph K hK v hv hV)
  obtain ⟨M, hM⟩ := finite_simplicial_model A (TopCat.of K.space) e
  refine ⟨M, ?_⟩
  intro j
  exact (hM j).trans (Nat.card_congr
    ((faceComplex_nondegenerateEquiv P j).trans (indexedFaces_degreeEquiv K v hv hV j)))

example : Module.finrank ℤ (Fin 3 → ℤ) = 3 := by simp

/-- Compact semialgebraic spaces have finite integral models and finitely generated integral H₁.
Source: Coste, An Introduction to Semialgebraic Geometry (2002), Theorem 4.4; Hatcher, §2.2. -/
theorem semialgebraic_finite_aux {n : ℕ}
    (f : HodgeLean.Foundations.Program.s2v_t11b_Formula n)
    (hf : IsCompact f.realize) :
    Nonempty (FiniteChainModel (TopCat.of f.realize)) ∧
      Module.Finite ℤ (H1 (TopCat.of f.realize)) ∧
      Module.Finite ℤ (Lattice (TopCat.of f.realize)) ∧
      Module.Free ℤ (Lattice (TopCat.of f.realize)) := by
  obtain ⟨K, hK, h, _⟩ :=
    Semialgebraic.CompatibleTriangulation.compact_compatible_triangulation n f hf
      (fun j : Fin 0 => Fin.elim0 j)
  obtain ⟨M, _⟩ := triangulated_model_aux n K hK
  let e : TopCat.of K.space ≅ TopCat.of f.realize := TopCat.isoOfHomeo h
  let N := M.transport e
  obtain ⟨h1, h2, h3⟩ := N.lattice_finiteFree
  exact ⟨⟨N⟩, h1, h2, h3⟩

example : Module.Finite ℤ (Fin 2 → ℤ) := inferInstance

/-- The degree-one integral universal coefficient map identifies cohomology with the dual of the actual torsion quotient.
Source: Hatcher, Algebraic Topology, Theorem 3.2; H₀ is free. -/
theorem integral_uct_aux (X : TopCat.{0}) :
    ∃ e : Cohomology ℤ X 1 ≃ₗ[ℤ] Module.Dual ℤ (Lattice X),
      ∀ u a, e u (Submodule.Quotient.mk a) = evaluation ℤ X u a := by
  have hmod : (Submodule.Quotient.module (Submodule.torsion ℤ (H1 X)) :
      Module ℤ (Lattice X)) = AddCommGroup.toIntModule (Lattice X) :=
    Subsingleton.elim _ _
  rw [← hmod]
  let i := LinearEquiv.ofBijective (evaluation ℤ X) (integralEvaluation_bijective X)
  refine ⟨i.trans torsionQuotientDual, ?_⟩
  intro u a
  exact torsionQuotientDual_apply (i u) a

example : (LinearMap.fst ℤ ℤ ℤ : Module.Dual ℤ (ℤ × ℤ)) (3, 5) = 3 := rfl

/-- Integral evaluation commutes with continuous pullback and actual integral pushforward.
Source: Hatcher, Algebraic Topology, §3.1, naturality of the Kronecker pairing. -/
theorem integral_evaluation_natural_aux {X Y : TopCat.{0}} (f : X ⟶ Y)
    (u : Cohomology ℤ Y 1) (a : H1 X) :
    evaluation ℤ X (cohomologyMap ℤ 1 f u) a =
      evaluation ℤ Y u (mapH1 f a) := by
  exact evaluation_natural ℤ f u a

example : (LinearMap.fst ℤ ℤ ℤ).comp
    (LinearEquiv.prodComm ℤ ℤ ℤ).toLinearMap (2, 7) = 7 := rfl

/-- Finite integral H₁ permits rational extension of integral degree-one cohomology with the evaluation normalization fixed.
Source: Hatcher, Algebraic Topology, Theorems 3.2 and 3.3, and §3.A. -/
theorem rational_dual_comparison_aux (X : TopCat.{0}) [Module.Finite ℤ (H1 X)]
    (c : ZChains X ⟶ RestrictedQChains X)
    (hc : ∀ n z, (c.f n).hom z = coefficient X n z) :
    ∃ e : (ℚ ⊗[ℤ] Cohomology ℤ X 1) ≃ₗ[ℚ] Cohomology ℚ X 1,
      ∀ u a, evaluation ℚ X (e (1 ⊗ₜ[ℤ] u)) (coefficientH1 X c a) =
        (evaluation ℤ X u a : ℚ) := by
  obtain ⟨i, hi⟩ := integral_uct_aux X
  obtain ⟨r, hr⟩ := rationalComparison X c hc
  obtain ⟨hf, hfree⟩ := IntegralHomology.lattice_finiteFree X
  letI := hf
  letI := hfree
  let b := (TensorProduct.isBaseChange ℤ (Lattice X) ℚ).toDualBaseChange
  let e := (LinearEquiv.baseChange ℤ ℚ _ _ i).trans (b.trans
    (r.dualMap.symm.trans (cohomologyEquivDualHomology ℚ X 1).symm))
  refine ⟨e, ?_⟩
  intro u a
  change (cohomologyEquivDualHomology ℚ X 1
    ((cohomologyEquivDualHomology ℚ X 1).symm
      (r.dualMap.symm (b ((LinearEquiv.baseChange ℤ ℚ _ _ i) (1 ⊗ₜ[ℤ] u))))))
      (coefficientH1 X c a) = _
  rw [LinearEquiv.apply_symm_apply, ← hr a]
  have hdual := LinearMap.congr_fun (r.dualMap.apply_symm_apply
    (b ((LinearEquiv.baseChange ℤ ℚ _ _ i) (1 ⊗ₜ[ℤ] u))))
    (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice X))
  change r.dualMap.symm (b ((LinearEquiv.baseChange ℤ ℚ _ _ i) (1 ⊗ₜ[ℤ] u)))
    (r (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice X))) = _ at hdual
  refine hdual.trans ?_
  rw [LinearEquiv.baseChange_tmul]
  have hb := (TensorProduct.isBaseChange ℤ (Lattice X) ℚ).toDualBaseChange_tmul
    1 (i u) (Submodule.Quotient.mk a)
  change b (1 ⊗ₜ[ℤ] i u) (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice X)) = _ at hb
  simpa only [one_mul, hi, algebraMap_int_eq, Int.coe_castRingHom] using hb

example : (IsBaseChange.linearMap ℤ ℚ).equiv
    ((1 : ℚ) ⊗ₜ[ℤ] (3 : ℤ)) = 3 := by
  rw [IsBaseChange.equiv_tmul]
  norm_num

/-- Every normalized rational dual comparison respects contravariant continuous pullback.
Source: Hatcher, Algebraic Topology, §3.1 and §3.A. -/
theorem rational_dual_natural_aux {X Y : TopCat.{0}} (f : X ⟶ Y)
    (cX : ZChains X ⟶ RestrictedQChains X)
    (cY : ZChains Y ⟶ RestrictedQChains Y)
    (hcX : ∀ n z, (cX.f n).hom z = coefficient X n z)
    (hcY : ∀ n z, (cY.f n).hom z = coefficient Y n z)
    (eX : (ℚ ⊗[ℤ] Cohomology ℤ X 1) ≃ₗ[ℚ] Cohomology ℚ X 1)
    (eY : (ℚ ⊗[ℤ] Cohomology ℤ Y 1) ≃ₗ[ℚ] Cohomology ℚ Y 1)
    (heX : ∀ u a, evaluation ℚ X (eX (1 ⊗ₜ[ℤ] u)) (coefficientH1 X cX a) =
      (evaluation ℤ X u a : ℚ))
    (heY : ∀ u a, evaluation ℚ Y (eY (1 ⊗ₜ[ℤ] u)) (coefficientH1 Y cY a) =
      (evaluation ℤ Y u a : ℚ)) (t : ℚ ⊗[ℤ] Cohomology ℤ Y 1) :
    eX ((cohomologyMap ℤ 1 f).baseChange ℚ t) = cohomologyMap ℚ 1 f (eY t) := by
  apply (cohomologyEquivDualHomology ℚ X 1).injective
  apply (coefficient_baseChange X cX hcX).algHom_ext
  intro a
  change evaluation ℚ X (eX ((cohomologyMap ℤ 1 f).baseChange ℚ t))
    (coefficientH1 X cX a) = evaluation ℚ X (cohomologyMap ℚ 1 f (eY t))
    (coefficientH1 X cX a)
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearEquiv.map_zero, LinearMap.zero_apply]
  | add t t' ht ht' =>
      simp only [map_add, LinearEquiv.map_add, LinearMap.add_apply, ht, ht']
  | tmul r u =>
      have hunit : evaluation ℚ X
          (eX ((cohomologyMap ℤ 1 f).baseChange ℚ (1 ⊗ₜ[ℤ] u)))
          (coefficientH1 X cX a) =
          evaluation ℚ X (cohomologyMap ℚ 1 f (eY (1 ⊗ₜ[ℤ] u)))
          (coefficientH1 X cX a) := by
        have hcoeff : coefficientH1 Y cY (mapH1 f a) =
            homologyMap ℚ 1 f (coefficientH1 X cX a) :=
          coefficient_natural f cX cY hcX hcY a
        rw [LinearMap.baseChange_tmul, heX, evaluation_natural ℚ,
          ← hcoeff, heY, integral_evaluation_natural_aux]
      have htensor : r ⊗ₜ[ℤ] u = r • (1 ⊗ₜ[ℤ] u) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [htensor]
      simp only [map_smul, LinearEquiv.map_smul, LinearMap.smul_apply]
      exact congrArg (fun z => r • z) hunit

example : (LinearEquiv.prodComm ℚ ℚ ℚ).toLinearMap.dualMap
    (LinearMap.fst ℚ ℚ ℚ) (2, 7) = 7 := rfl

/-- The rational singular/sheaf comparison identifies actual HQ¹ with the rational lattice dual and fixes integral evaluation.
Source: Bredon, Sheaf Theory, second edition, III.1; Hatcher, §3.1 and §3.A. -/
theorem hq_lattice_dual_aux (X : Over (Spec ↧ℂ))
    (hX : ∀ (x : ComplexPoint X) (U : Opens (ComplexPoint X)), x ∈ U →
      ∃ V : Opens (ComplexPoint X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (c : ZChains (TopCat.of (ComplexPoint X)) ⟶
      RestrictedQChains (TopCat.of (ComplexPoint X)))
    (hc : ∀ n z, (c.f n).hom z = coefficient (TopCat.of (ComplexPoint X)) n z) :
    ∃ e : HQ X 1 ≃ₗ[ℚ] Module.Dual ℚ
        (ℚ ⊗[ℤ] Lattice (TopCat.of (ComplexPoint X))),
      ∀ v a, e (HodgeLean.Adapters.RationalSheafComparison.comparison X hX 1 v)
        (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice (TopCat.of (ComplexPoint X)))) =
          evaluation ℚ (TopCat.of (ComplexPoint X)) v
            (coefficientH1 (TopCat.of (ComplexPoint X)) c a) := by
  obtain ⟨r, hr⟩ := rationalComparison (TopCat.of (ComplexPoint X)) c hc
  obtain ⟨_, s, hs⟩ :=
    HodgeLean.Topology.RationalSheafComparison.comparison_linearEquiv
      (TopCat.of (ComplexPoint X)) hX 1
  refine ⟨s.symm.trans ((cohomologyEquivDualHomology ℚ
    (TopCat.of (ComplexPoint X)) 1).trans r.dualMap), ?_⟩
  intro v a
  change (cohomologyEquivDualHomology ℚ _ 1 (s.symm
    (HodgeLean.Adapters.RationalSheafComparison.comparison X hX 1 v)))
    (r (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice _))) = _
  rw [hr]
  have hv : HodgeLean.Adapters.RationalSheafComparison.comparison X hX 1 v = s v :=
    (hs v).symm
  rw [hv, s.symm_apply_apply]
  rfl

example : (LinearMap.fst ℚ ℚ ℚ : Module.Dual ℚ (ℚ × ℚ)) (3, 5) = 3 := rfl

/-- The normalized HQ¹ lattice duals retain the actual project pullback square on every rational tensor.
Source: Bredon, Sheaf Theory, second edition, III.1; Hatcher, §3.A. -/
theorem hq_lattice_dual_natural_aux {X Y : Over (Spec ↧ℂ)} (q : X ⟶ Y)
    (hX : ∀ (x : ComplexPoint X) (U : Opens (ComplexPoint X)), x ∈ U →
      ∃ V : Opens (ComplexPoint X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hY : ∀ (y : ComplexPoint Y) (U : Opens (ComplexPoint Y)), y ∈ U →
      ∃ V : Opens (ComplexPoint Y), y ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    [T2Space (ComplexPoint X)] [T2Space (ComplexPoint Y)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    [∀ U : Opens (ComplexPoint Y), ParacompactSpace U]
    (cX : ZChains (TopCat.of (ComplexPoint X)) ⟶ RestrictedQChains (TopCat.of (ComplexPoint X)))
    (cY : ZChains (TopCat.of (ComplexPoint Y)) ⟶ RestrictedQChains (TopCat.of (ComplexPoint Y)))
    (hcX : ∀ n z, (cX.f n).hom z = coefficient (TopCat.of (ComplexPoint X)) n z)
    (hcY : ∀ n z, (cY.f n).hom z = coefficient (TopCat.of (ComplexPoint Y)) n z)
    (eX : HQ X 1 ≃ₗ[ℚ] Module.Dual ℚ (ℚ ⊗[ℤ] Lattice (TopCat.of (ComplexPoint X))))
    (eY : HQ Y 1 ≃ₗ[ℚ] Module.Dual ℚ (ℚ ⊗[ℤ] Lattice (TopCat.of (ComplexPoint Y))))
    (heX : ∀ v a, eX (HodgeLean.Adapters.RationalSheafComparison.comparison X hX 1 v)
      (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice (TopCat.of (ComplexPoint X)))) =
        evaluation ℚ (TopCat.of (ComplexPoint X)) v (coefficientH1 _ cX a))
    (heY : ∀ v a, eY (HodgeLean.Adapters.RationalSheafComparison.comparison Y hY 1 v)
      (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice (TopCat.of (ComplexPoint Y)))) =
        evaluation ℚ (TopCat.of (ComplexPoint Y)) v (coefficientH1 _ cY a))
    (u : HQ Y 1) (t : ℚ ⊗[ℤ] Lattice (TopCat.of (ComplexPoint X))) :
    eX (HodgeLean.Adapters.RationalSheafComparison.pullback q 1 u) t =
      eY u ((mapLattice (TopCat.ofHom (Point.continuousMap q))).baseChange ℚ t) := by
  obtain ⟨v, hv⟩ :=
    (HodgeLean.Topology.RationalSheafComparison.comparison_linearEquiv
      (TopCat.of (ComplexPoint Y)) hY 1).1.2 u
  change HodgeLean.Adapters.RationalSheafComparison.comparison Y hY 1 v = u at hv
  subst u
  have hn := HodgeLean.Topology.RationalSheafComparison.comparison_naturality
    (TopCat.of (ComplexPoint X)) hX (TopCat.of (ComplexPoint Y)) hY
    (TopCat.ofHom (Point.continuousMap q)) 1 v
  change HodgeLean.Adapters.RationalSheafComparison.comparison X hX 1
    (cohomologyMap ℚ 1 (TopCat.ofHom (Point.continuousMap q)) v) =
      HodgeLean.Adapters.RationalSheafComparison.pullback q 1
        (HodgeLean.Adapters.RationalSheafComparison.comparison Y hY 1 v) at hn
  rw [← hn]
  obtain ⟨rX, hrX⟩ := rationalComparison (TopCat.of (ComplexPoint X)) cX hcX
  obtain ⟨rY, hrY⟩ := rationalComparison (TopCat.of (ComplexPoint Y)) cY hcY
  have hx (w : Cohomology ℚ (TopCat.of (ComplexPoint X)) 1) :
      eX (HodgeLean.Adapters.RationalSheafComparison.comparison X hX 1 w) =
        rX.dualMap (cohomologyEquivDualHomology ℚ _ 1 w) := by
    apply (TensorProduct.isBaseChange ℤ (Lattice (TopCat.of (ComplexPoint X))) ℚ).algHom_ext
    intro a
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    change eX (HodgeLean.Adapters.RationalSheafComparison.comparison X hX 1 w)
      (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice _)) =
        (cohomologyEquivDualHomology ℚ _ 1 w)
          (rX (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice _)))
    rw [heX, hrX]
    rfl
  have hy (w : Cohomology ℚ (TopCat.of (ComplexPoint Y)) 1) :
      eY (HodgeLean.Adapters.RationalSheafComparison.comparison Y hY 1 w) =
        rY.dualMap (cohomologyEquivDualHomology ℚ _ 1 w) := by
    apply (TensorProduct.isBaseChange ℤ (Lattice (TopCat.of (ComplexPoint Y))) ℚ).algHom_ext
    intro a
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    change eY (HodgeLean.Adapters.RationalSheafComparison.comparison Y hY 1 w)
      (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice _)) =
        (cohomologyEquivDualHomology ℚ _ 1 w)
          (rY (1 ⊗ₜ[ℤ] (Submodule.Quotient.mk a : Lattice _)))
    rw [heY, hrY]
    rfl
  rw [hx, hy]
  change (cohomologyEquivDualHomology ℚ _ 1
    (cohomologyMap ℚ 1 (TopCat.ofHom (Point.continuousMap q)) v)) (rX t) =
      (cohomologyEquivDualHomology ℚ _ 1 v)
        (rY ((mapLattice (TopCat.ofHom (Point.continuousMap q))).baseChange ℚ t))
  rw [cohomologyEquivDualHomology_cohomologyMap]
  exact congrArg (cohomologyEquivDualHomology ℚ _ 1 v)
    (rationalComparison_natural (TopCat.ofHom (Point.continuousMap q))
      cX cY hcX hcY rX rY hrX hrY t).symm

example : (LinearMap.fst ℚ ℚ ℚ).comp
    (LinearEquiv.prodComm ℚ ℚ ℚ).toLinearMap (2, 7) = 7 := rfl

end HodgeLean.Foundations.IntegralHomology.StageTwo
