import HodgeLean.Adapters.KleimanProductDefs
import HodgeLean.Adapters.CycleClassDivisorLocal
import HodgeLean.RealDefs.ComplexFundamentalClassParts.C_OpenLift

/-! # Coordinate products in every normal dimension

Associativity and the unit law of the relative cup `ccm15_relativeCup`, proved by evaluating
both sides on explicit relative cycles, and the induction from the divisor case
`ccm17_coordinate_product` to coordinate products of every normal dimension.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
-- File-wide: nine declarations here need definitional unfolding across the relative-cup and
-- supported-class wrappers, too many to scope one by one; this affects elaboration only, not
-- kernel checking.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
open AlgebraicTopology.Simplicial HodgeLean.Foundations.Singular HodgeLean.RealDefs

namespace HodgeLean.Adapters

attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData

/-! ## Dual classes and evaluation -/

private def hc9kc_dualEquiv (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :=
  (ShortComplex.homologyMapIso
    (HomologicalComplex.linearDualCochainComplexScIso K n)).toLinearEquiv.symm

private def hc9kc_dualClass (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :=
  (hc9kc_dualEquiv K n).toLinearMap.comp (K.sc n).linearDual.moduleCatHomologyClass

private theorem hc9kc_dualClass_surjective (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    Function.Surjective (hc9kc_dualClass K n) :=
  (hc9kc_dualEquiv K n).surjective.comp (K.sc n).linearDual.moduleCatHomologyClass_surjective

private theorem hc9kc_dualClass_naturality
    {K L : ChainComplex (ModuleCat ℚ) ℕ} (f : K ⟶ L) (n : ℕ)
    (u : LinearMap.ker (L.sc n).linearDual.g.hom) :
    HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap f) n
        (hc9kc_dualClass L n u) =
      hc9kc_dualClass K n (ShortComplex.moduleCatCycleMap
        (ShortComplex.linearDualMap
          ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) n).map f)) u) := by
  apply (hc9kc_dualEquiv K n).symm.injective
  have h := congrArg (ShortComplex.homologyFunctor (ModuleCat ℚ)).map
    (HomologicalComplex.linearDualCochainComplexScIso_naturality f n)
  rw [Functor.map_comp, Functor.map_comp] at h
  have hh := ConcreteCategory.congr_hom h (hc9kc_dualClass L n u)
  change (hc9kc_dualEquiv K n).symm
      (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap f) n
        (hc9kc_dualClass L n u)) =
    (ShortComplex.homologyMap (ShortComplex.linearDualMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) n).map f))).hom
      ((hc9kc_dualEquiv L n).symm
      (hc9kc_dualClass L n u)) at hh
  rw [hh]
  simp only [hc9kc_dualClass, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]
  exact ShortComplex.moduleCatHomologyClass_naturality _ u

private theorem hc9kc_relativeCup_class (Y : TopCat.{0}) (S T : Closeds Y) (p q : ℕ)
    (u : LinearMap.ker (ccm15_relativeDual Y S p).g.hom)
    (v : LinearMap.ker (ccm15_relativeDual Y T q).g.hom) :
    ccm15_relativeCup Y S T p q
      (hc9kc_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (S : Set Y)ᶜ)) p u)
      (hc9kc_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (T : Set Y)ᶜ)) q v) =
    ccm15_dualTransport Y S T S.isClosed T.isClosed (p + q)
      ((ccm15_smallDual Y S T (p + q)).moduleCatHomologyClass
        (ccm15_cycleCup Y S T p q u v)) := by
  change ccm15_dualTransport Y S T S.isClosed T.isClosed (p + q)
    ((ccm15_smallDual Y S T (p + q)).moduleCatHomologyIso.inv.hom
      (ccm15_quotientCup Y S T p q
        ((ccm15_relativeDual Y S p).moduleCatHomologyIso.hom.hom
          ((hc9kc_dualEquiv _ p).symm (hc9kc_dualClass _ p u)))
        ((ccm15_relativeDual Y T q).moduleCatHomologyIso.hom.hom
          ((hc9kc_dualEquiv _ q).symm (hc9kc_dualClass _ q v))))) = _
  simp only [hc9kc_dualClass, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]
  have hu := ConcreteCategory.congr_hom
    (ccm15_relativeDual Y S p).moduleCatHomologyIso.inv_hom_id (Submodule.Quotient.mk u)
  have hv := ConcreteCategory.congr_hom
    (ccm15_relativeDual Y T q).moduleCatHomologyIso.inv_hom_id (Submodule.Quotient.mk v)
  change (ccm15_relativeDual Y S p).moduleCatHomologyIso.hom.hom
    ((ccm15_relativeDual Y S p).moduleCatHomologyClass u) = Submodule.Quotient.mk u at hu
  change (ccm15_relativeDual Y T q).moduleCatHomologyIso.hom.hom
    ((ccm15_relativeDual Y T q).moduleCatHomologyClass v) = Submodule.Quotient.mk v at hv
  rw [hu, hv]
  rfl

private theorem hc9kc_comparison_transport (Y : TopCat.{0}) (S T : Closeds Y)
    (n : ℕ) (w : (ccm15_smallDual Y S T n).homology) :
    HomologicalComplex.homologyMap
      (HomologicalComplex.linearDualMap (ccm14_relativeComparison Y S T)) n
      (ccm15_dualTransport Y S T S.isClosed T.isClosed n w) =
    hc9kc_dualEquiv (ccm14_smallRelativeComplex Y S T) n w := by
  have := ccm15_dualComparison_quasiIso_aux Y S T S.isClosed T.isClosed
  exact (asIso (HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap (ccm14_relativeComparison Y S T)) n)).toLinearEquiv.apply_symm_apply _

private theorem hc9kc_dualClass_evaluation
    (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (u : LinearMap.ker (K.sc n).f.hom.dualMap)
    (z : LinearMap.ker (K.sc n).g.hom) :
    K.linearDualHomologyEquiv n (hc9kc_dualClass K n u)
      ((K.sc n).moduleCatHomologyClass z) = (u.1 : Module.Dual ℚ (K.X n)) z.1 := by
  change (K.sc n).linearDualHomologyEquiv
    ((hc9kc_dualEquiv K n).symm (hc9kc_dualClass K n u)) _ = _
  simp only [hc9kc_dualClass, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]
  exact ShortComplex.linearDualHomologyEquiv_class_apply_class (K.sc n) u z

private theorem hc9kc_relativeCup_evaluation (Y : TopCat.{0})
    (S T : Closeds Y) (p q : ℕ)
    (u : LinearMap.ker (ccm15_relativeDual Y S p).g.hom)
    (v : LinearMap.ker (ccm15_relativeDual Y T q).g.hom)
    (z : LinearMap.ker ((ccm14_smallRelativeComplex Y S T).sc (p + q)).g.hom) :
    relativeCohomologyEquivDualHomology ℚ
      (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ) (p + q)
      (ccm15_relativeCup Y S T p q
        (hc9kc_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (S : Set Y)ᶜ)) p u)
        (hc9kc_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (T : Set Y)ᶜ)) q v))
      (HomologicalComplex.homologyMap (ccm14_relativeComparison Y S T) (p + q)
        (((ccm14_smallRelativeComplex Y S T).sc (p + q)).moduleCatHomologyClass z)) =
      ccm14_smallRelativeCup Y S T p q u.1 v.1 z.1 := by
  rw [hc9kc_relativeCup_class]
  change ((relativeChainFunctor ℚ).obj _).linearDualHomologyEquiv (p + q) _ _ = _
  refine (HomologicalComplex.linearDualHomologyEquiv_naturality
    (ccm14_relativeComparison Y S T) (p + q) _ _).symm.trans ?_
  rw [hc9kc_comparison_transport]
  exact hc9kc_dualClass_evaluation _ _ (ccm15_cycleCup Y S T p q u v) z

/-- The relative class of an explicit chain whose boundary vanishes in relative chains. -/
private def hc9kc_chainClass (P : TopPair.{0}) (n : ℕ)
    (c : ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).X n)
    (hc : (((relativeChainFunctor ℚ).obj P).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ P).f n).hom c) = 0) :
    RelativeHomology ℚ P n :=
  (((relativeChainFunctor ℚ).obj P).sc n).moduleCatHomologyClass ⟨_, hc⟩

/-- The comparison of an explicit small relative cycle is the class of its chain. -/
private theorem hc9kc_comparison_chainClass (Y : TopCat.{0}) (S T : Closeds Y) (n : ℕ)
    (x : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X n)
    (hx : ((ccm14_smallRelativeComplex Y S T).d n ((ComplexShape.down ℕ).next n)).hom
      (((ccm14_smallProjection Y S T).f n).hom x) = 0)
    (hx' : (((relativeChainFunctor ℚ).obj
        (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ)).d n
          ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ
        (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ)).f n).hom x) = 0) :
    HomologicalComplex.homologyMap (ccm14_relativeComparison Y S T) n
        (((ccm14_smallRelativeComplex Y S T).sc n).moduleCatHomologyClass ⟨_, hx⟩) =
      hc9kc_chainClass _ n x hx' := by
  unfold hc9kc_chainClass
  refine (ShortComplex.moduleCatHomologyClass_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) n).map
      (ccm14_relativeComparison Y S T)) _).trans ?_
  congr 1
  apply Subtype.ext
  have hfac := congrArg (fun g => g.f n)
    (cokernel.π_desc _ (relativeChainProjection ℚ
      (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ))
      _ : ccm14_smallProjection Y S T ≫ ccm14_relativeComparison Y S T = _)
  exact ConcreteCategory.congr_hom hfac x

/-- A small relative cycle is a relative cycle modulo the complement of the intersection. -/
private theorem hc9kc_relativeCycle_of_small (Y : TopCat.{0}) (S T : Closeds Y) (n : ℕ)
    (x : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X n)
    (hx : ((ccm14_smallRelativeComplex Y S T).d n ((ComplexShape.down ℕ).next n)).hom
      (((ccm14_smallProjection Y S T).f n).hom x) = 0) :
    (((relativeChainFunctor ℚ).obj
        (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ)).d n
          ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ
        (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ)).f n).hom x) = 0 := by
  have hfac := congrArg (fun g => g.f n)
    (cokernel.π_desc _ (relativeChainProjection ℚ
      (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ))
      _ : ccm14_smallProjection Y S T ≫ ccm14_relativeComparison Y S T = _)
  have hx2 := ConcreteCategory.congr_hom hfac x
  change ((ccm14_relativeComparison Y S T).f n).hom
    (((ccm14_smallProjection Y S T).f n).hom x) = _ at hx2
  rw [← hx2]
  have hcomm := ConcreteCategory.congr_hom
    ((ccm14_relativeComparison Y S T).comm n ((ComplexShape.down ℕ).next n))
    (((ccm14_smallProjection Y S T).f n).hom x)
  change (((relativeChainFunctor ℚ).obj _).d n _).hom
      (((ccm14_relativeComparison Y S T).f n).hom _) =
    ((ccm14_relativeComparison Y S T).f _).hom
      (((ccm14_smallRelativeComplex Y S T).d n _).hom _) at hcomm
  refine hcomm.trans ?_
  rw [hx, map_zero]

/-- Evaluation of a relative cup on the class of an explicit chain whose boundary is small. -/
private theorem hc9kc_relativeCup_eval (Y : TopCat.{0}) (S T : Closeds Y) (p q : ℕ)
    (u : LinearMap.ker (ccm15_relativeDual Y S p).g.hom)
    (v : LinearMap.ker (ccm15_relativeDual Y T q).g.hom)
    (x : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X (p + q))
    (hx : ((ccm14_smallRelativeComplex Y S T).d (p + q)
      ((ComplexShape.down ℕ).next (p + q))).hom
        (((ccm14_smallProjection Y S T).f (p + q)).hom x) = 0) :
    relativeCohomologyEquivDualHomology ℚ
      (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ) (p + q)
      (ccm15_relativeCup Y S T p q
        (hc9kc_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (S : Set Y)ᶜ)) p u)
        (hc9kc_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (T : Set Y)ᶜ)) q v))
      (hc9kc_chainClass _ (p + q) x (hc9kc_relativeCycle_of_small Y S T (p + q) x hx)) =
      ccm13_relativeCupLift Y S T p q u.1 v.1 x := by
  refine (congrArg _ (hc9kc_comparison_chainClass Y S T (p + q) x hx _).symm).trans ?_
  refine (hc9kc_relativeCup_evaluation Y S T p q u v ⟨_, hx⟩).trans ?_
  exact LinearMap.congr_fun (ccm15_smallCup_projection Y S T p q u.1 v.1) x

/-! ## Representatives with small boundary -/

private theorem hc9kc_chainClass_eq_homologyπ (P : TopPair.{0}) (n : ℕ)
    (c : ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).X n)
    (hc : (((relativeChainFunctor ℚ).obj P).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ P).f n).hom c) = 0)
    (z : ((relativeChainFunctor ℚ).obj P).cycles n)
    (hz : (((relativeChainFunctor ℚ).obj P).iCycles n).hom z =
      ((relativeChainProjection ℚ P).f n).hom c) :
    hc9kc_chainClass P n c hc = (((relativeChainFunctor ℚ).obj P).homologyπ n).hom z := by
  let S := ((relativeChainFunctor ℚ).obj P).sc n
  have h1 : hc9kc_chainClass P n c hc =
      (S.moduleCatCyclesIso.inv ≫ S.homologyπ).hom ⟨_, hc⟩ := by
    rw [ShortComplex.moduleCatCyclesIso_inv_π]
    rfl
  rw [h1]
  change S.homologyπ.hom (S.moduleCatCyclesIso.inv.hom ⟨_, hc⟩) = S.homologyπ.hom z
  congr 1
  apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles_apply]
  exact hz.symm

open scoped Simplicial in
/-- Chains spanned by simplices lying in one member of a family of subsets. -/
private def hc9kc_smallSpan (Y : TopCat.{0}) {ι : Type} (F : ι → Set Y) (n : ℕ) :
    Submodule ℚ (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X n) :=
  Submodule.span ℚ {c | ∃ (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (i : ι),
    (∀ t, Y.toSSetObjEquiv _ σ t ∈ F i) ∧ chainOfSimplex ℚ σ = c}

open scoped Simplicial in
private theorem hc9kc_smallSpan_le_ker (Y : TopCat.{0}) {ι : Type} (F : ι → Set Y) (n : ℕ)
    {M : Type} [AddCommGroup M] [Module ℚ M]
    (φ : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X n →ₗ[ℚ] M)
    (h : ∀ (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (i : ι),
      (∀ t, Y.toSSetObjEquiv _ σ t ∈ F i) → φ (chainOfSimplex ℚ σ) = 0) :
    hc9kc_smallSpan Y F n ≤ LinearMap.ker φ := by
  rw [hc9kc_smallSpan, Submodule.span_le]
  rintro _ ⟨σ, i, hσ, rfl⟩
  exact h σ i hσ

/-- Small chains of the complement, pushed into the ambient space, have simplices in
the family. -/
private theorem hc9kc_smallInclusion_mem (Y : TopCat.{0}) (K : Set Y)
    {ι : Type} (F : ι → Set Y) (k : ℕ)
    (w : ((coverSmallSingularSubcomplex (TopCat.of ↥Kᶜ)
      (fun i => {y : ↥Kᶜ | y.1 ∈ F i}) : SSet).chainComplex (ModuleCat.of ℚ ℚ)).X k) :
    ((SSet.chainComplexMap (TopCat.toSSet.map (topologicalSubsetInclusion Y Kᶜ))
      (ModuleCat.of ℚ ℚ)).f k).hom
        (((coverSmallRationalSingularChainInclusion (TopCat.of ↥Kᶜ)
          (fun i => {y : ↥Kᶜ | y.1 ∈ F i})).f k).hom w) ∈ hc9kc_smallSpan Y F k := by
  have hw := C_chain_mem_iSup_range _ k w
  suffices hle : (⨆ σ, LinearMap.range ((coverSmallSingularSubcomplex (TopCat.of ↥Kᶜ)
      (fun i => {y : ↥Kᶜ | y.1 ∈ F i}) : SSet).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) σ).hom) ≤
      (hc9kc_smallSpan Y F k).comap
        (((SSet.chainComplexMap (TopCat.toSSet.map (topologicalSubsetInclusion Y Kᶜ))
          (ModuleCat.of ℚ ℚ)).f k).hom.comp
          ((coverSmallRationalSingularChainInclusion (TopCat.of ↥Kᶜ)
            (fun i => {y : ↥Kᶜ | y.1 ∈ F i})).f k).hom) from hle hw
  refine iSup_le fun σ => ?_
  rintro _ ⟨r, rfl⟩
  obtain ⟨i, τ, hτ⟩ := (mem_coverSmallSingularSubcomplex_iff_exists_preimage
    (TopCat.of ↥Kᶜ) (fun i => {y : ↥Kᶜ | y.1 ∈ F i}) σ.1).mp σ.2
  have hr : ((coverSmallSingularSubcomplex (TopCat.of ↥Kᶜ)
      (fun i => {y : ↥Kᶜ | y.1 ∈ F i}) : SSet).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom r =
      r • chainOfSimplex ℚ σ := by
    rw [chainOfSimplex, ← map_smul]
    simp
  simp only [Submodule.mem_comap, LinearMap.comp_apply]
  rw [hr, map_smul, map_smul]
  apply Submodule.smul_mem
  change ((SSet.chainComplexMap (TopCat.toSSet.map (topologicalSubsetInclusion Y Kᶜ))
      (ModuleCat.of ℚ ℚ)).f k).hom (((SSet.chainComplexMap
        (coverSmallSingularSubcomplex (TopCat.of ↥Kᶜ)
          (fun i => {y : ↥Kᶜ | y.1 ∈ F i})).ι (ModuleCat.of ℚ ℚ)).f k).hom
        (chainOfSimplex ℚ σ)) ∈ _
  rw [chainOfSimplex_map, chainOfSimplex_map]
  apply Submodule.subset_span
  refine ⟨_, i, fun t => ?_, rfl⟩
  have hv := congrArg (fun s => ((TopCat.of ↥Kᶜ).toSSetObjEquiv _ s t)) hτ
  change ((TopCat.of ↥Kᶜ).toSSetObjEquiv _ σ.1 t).1 ∈ F i
  rw [← hv]
  exact ((TopCat.of _).toSSetObjEquiv _ τ t).2

/-- Every relative class modulo the complement of `K` is represented by a chain whose boundary
consists of simplices lying in members of an open cover of that complement. -/
private theorem hc9kc_exists_small_representative (Y : TopCat.{0}) (K : Set Y)
    {ι : Type} (F : ι → Set Y) (hopen : ∀ i, IsOpen (F i)) (hcover : ⋃ i, F i = Kᶜ)
    (n : ℕ) (h : RelativeHomology ℚ (TopPair.ofSubset (X := Y) Kᶜ) n) :
    ∃ (x : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X n)
      (hx : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := Y) Kᶜ)).d n
          ((ComplexShape.down ℕ).next n)).hom
        (((relativeChainProjection ℚ (TopPair.ofSubset (X := Y) Kᶜ)).f n).hom x) = 0),
      hc9kc_chainClass _ n x hx = h ∧
      (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d n
        ((ComplexShape.down ℕ).next n)).hom x ∈
          hc9kc_smallSpan Y F ((ComplexShape.down ℕ).next n) := by
  let P := TopPair.ofSubset (X := Y) Kᶜ
  let Q := (relativeChainFunctor ℚ).obj P
  let C := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)
  let L := (TopCat.toSSet.obj (TopCat.of ↥Kᶜ)).chainComplex (ModuleCat.of ℚ ℚ)
  let πP : C ⟶ Q := relativeChainProjection ℚ P
  let incl : L ⟶ C :=
    SSet.chainComplexMap (TopCat.toSSet.map (topologicalSubsetInclusion Y Kᶜ)) (ModuleCat.of ℚ ℚ)
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (Q.homologyπ n)).mp inferInstance h
  let j := (ComplexShape.down ℕ).next n
  obtain ⟨z, hz⟩ : ∃ z : C.X n, (πP.f n).hom z = (Q.iCycles n).hom c :=
    C_relativeChainProjection_surjective P n ((Q.iCycles n).hom c)
  have hdc : (Q.d n j).hom ((Q.iCycles n).hom c) = 0 := by
    have h2 := congrArg (fun q => q.hom c) (Q.iCycles_d n j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h2
  have hrel : (Q.d n j).hom ((πP.f n).hom z) = 0 := (congrArg (Q.d n j).hom hz).trans hdc
  have hdz : (πP.f j).hom ((C.d n j).hom z) = 0 := by
    have h1 := congrArg (fun q => q.hom z) (πP.comm n j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    exact h1.symm.trans hrel
  have hπincl : ∀ k (b : L.X k), (πP.f k).hom ((incl.f k).hom b) = 0 := by
    intro k b
    have h0 := congrArg (fun g => (g.f k).hom b)
      (cokernel.condition ((chainPairFunctor ℚ).obj P).hom)
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply] at h0
    exact h0
  have hclass : ∀ (x : C.X n) (hx : (Q.d n j).hom ((πP.f n).hom x) = 0),
      (πP.f n).hom x = (Q.iCycles n).hom c →
      hc9kc_chainClass P n x hx = (Q.homologyπ n).hom c := fun x hx hxc =>
    hc9kc_chainClass_eq_homologyπ P n x hx c hxc.symm
  by_cases hn : (ComplexShape.down ℕ).Rel n j
  · obtain ⟨b, hb⟩ : ∃ b : L.X j, (incl.f j).hom b = (C.d n j).hom z :=
      C_relativeChainProjection_exact P j _ hdz
    have hmono : Mono ((chainPairFunctor ℚ).obj P).hom := relativeChainMap_mono ℚ P
    have hinj : ∀ k, Function.Injective (incl.f k).hom := fun k =>
      (ModuleCat.mono_iff_injective (((chainPairFunctor ℚ).obj P).hom.f k)).mp inferInstance
    have hbcycle : (L.d j ((ComplexShape.down ℕ).next j)).hom b = 0 := by
      apply hinj
      have hc1 := congrArg (fun q => q.hom b) (incl.comm j ((ComplexShape.down ℕ).next j))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc1
      rw [← hc1, map_zero, hb]
      have hdd := congrArg (fun q => q.hom z) (C.d_comp_d n j ((ComplexShape.down ℕ).next j))
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using hdd
    let G : ι → Set (TopCat.of ↥Kᶜ) := fun i => {y : ↥Kᶜ | y.1 ∈ F i}
    have hGopen : ∀ i, IsOpen (G i) := fun i => (hopen i).preimage continuous_subtype_val
    have hGcover : ⋃ i, G i = Set.univ := by
      apply Set.eq_univ_of_forall
      intro y
      have hy : y.1 ∈ ⋃ i, F i := by rw [hcover]; exact y.2
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    let e := coverSmallRationalChainHomotopyEquiv_of_openCover (TopCat.of ↥Kᶜ) G hGopen hGcover
    have he : e.hom = coverSmallRationalSingularChainInclusion (TopCat.of ↥Kᶜ) G :=
      coverSmallRationalChainHomotopyEquiv_of_openCover_hom _ _ _ _
    let H := e.homotopyInvHomId
    have hcomm := congrArg (fun g => g.hom b) (H.comm j)
    rw [prevD_eq _ hn] at hcomm
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.id_f, ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at hcomm
    have hnext : (dNext j H.hom).hom b = 0 := by
      change (H.hom _ j).hom ((L.d j _).hom b) = 0
      rw [hbcycle, map_zero]
    rw [hnext, zero_add] at hcomm
    let a := (H.hom j n).hom b
    have hx0 : (πP.f n).hom (z + (incl.f n).hom a) = (Q.iCycles n).hom c := by
      rw [map_add, hπincl, add_zero, hz]
    have hx1 : (Q.d n j).hom ((πP.f n).hom (z + (incl.f n).hom a)) = 0 := by
      rw [hx0]
      exact hdc
    refine ⟨z + (incl.f n).hom a, hx1, hclass _ hx1 hx0, ?_⟩
    change (C.d n j).hom (z + (incl.f n).hom a) ∈ _
    rw [map_add, ← hb]
    have hc2 := congrArg (fun q => q.hom a) (incl.comm n j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc2
    rw [hc2, ← map_add, add_comm]
    change (incl.f j).hom ((L.d n j).hom a + b) ∈ _
    rw [← hcomm, he]
    exact hc9kc_smallInclusion_mem Y K F j _
  · have hx0 : (πP.f n).hom z = (Q.iCycles n).hom c := hz
    refine ⟨z, hrel, hclass _ hrel hx0, ?_⟩
    change (C.d n j).hom z ∈ _
    rw [C.shape n j hn, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _

/-! ## Cochain-level facts used for associativity -/

open scoped Simplicial in
private theorem hc9kc_frontFace_mem (Y : TopCat.{0}) {p q : ℕ}
    (σ : (TopCat.toSSet.obj Y) _⦋p + q⦌) (A : Set Y)
    (hσ : ∀ t, Y.toSSetObjEquiv _ σ t ∈ A) :
    ∀ t, Y.toSSetObjEquiv _ (frontFace (TopCat.toSSet.obj Y) (p := p) (q := q) σ) t ∈ A :=
  fun _ => hσ _

open scoped Simplicial in
private theorem hc9kc_backFace_mem (Y : TopCat.{0}) {p q : ℕ}
    (σ : (TopCat.toSSet.obj Y) _⦋p + q⦌) (A : Set Y)
    (hσ : ∀ t, Y.toSSetObjEquiv _ σ t ∈ A) :
    ∀ t, Y.toSSetObjEquiv _ (backFace (TopCat.toSSet.obj Y) (p := p) (q := q) σ) t ∈ A :=
  fun _ => hσ _

open scoped Simplicial in
/-- A relative cochain vanishes on a simplex lying in the subspace. -/
private theorem hc9kc_relativeCochain_simplex_zero (Y : TopCat.{0}) (B : Set Y) (k : ℕ)
    (v : RelativeCochain ℚ (TopPair.ofSubset (X := Y) B) k)
    (σ : (TopCat.toSSet.obj Y) _⦋k⦌) (hσ : ∀ t, Y.toSSetObjEquiv _ σ t ∈ B) :
    relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := Y) B) k v (chainOfSimplex ℚ σ) = 0 := by
  let τ := ((TopCat.of ↥B).toSSetObjEquiv _).symm
    ⟨fun t => ⟨Y.toSSetObjEquiv _ σ t, hσ t⟩, by fun_prop⟩
  have hτ : (TopCat.toSSet.map (TopPair.ofSubset (X := Y) B).map).app _ τ = σ := by
    apply (Y.toSSetObjEquiv _).injective
    rfl
  have h := LinearMap.congr_fun
    (cochainMap_relativeCochainToAbsolute_eq_zero ℚ (TopPair.ofSubset (X := Y) B) k v)
    (chainOfSimplex ℚ τ)
  simpa only [cochainMap_apply, chainOfSimplex_map, hτ, LinearMap.zero_apply] using h

open scoped Simplicial in
/-- A simplex lying in either complement maps to zero in the small quotient. -/
private theorem hc9kc_smallProjection_simplex_zero (Y : TopCat.{0})
    (S T : Set Y) {n : ℕ} (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (b : Bool)
    (hσ : ∀ t, Y.toSSetObjEquiv _ σ t ∈ ccm13_complementFamily Y S T b) :
    ((ccm14_smallProjection Y S T).f n).hom (chainOfSimplex ℚ σ) = 0 := by
  have hmem : σ ∈ (coverSmallSingularSubcomplex Y
      (ccm13_complementFamily Y S T)).obj (.op (.mk n)) := by
    apply (mem_coverSmallSingularSubcomplex_iff_exists_preimage Y _ σ).mpr
    let τ := ((TopCat.of (ccm13_complementFamily Y S T b)).toSSetObjEquiv _).symm
      ⟨fun t => ⟨Y.toSSetObjEquiv _ σ t, hσ t⟩, by fun_prop⟩
    refine ⟨b, τ, ?_⟩
    apply (Y.toSSetObjEquiv _).injective
    rfl
  let τ : (coverSmallSingularSubcomplex Y (ccm13_complementFamily Y S T) : SSet) _⦋n⦌ :=
    ⟨σ, hmem⟩
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) (cokernel.condition (ccm14_smallInclusion Y S T)))
    (chainOfSimplex ℚ τ)
  change ((ccm14_smallProjection Y S T).f n).hom
    (((ccm14_smallInclusion Y S T).f n).hom (chainOfSimplex ℚ τ)) = 0 at h
  have hi : (coverSmallSingularSubcomplex Y
      (ccm13_complementFamily Y S T)).ι.app _ τ = σ := rfl
  simpa only [ccm14_smallInclusion, coverSmallRationalSingularChainInclusion,
    chainOfSimplex_map, hi] using h

/-- A relative cocycle precomposed with any incoming differential vanishes. -/
private theorem hc9kc_cocycle_comp_d (Y : TopCat.{0}) (B : Set Y) (k i : ℕ)
    (w : LinearMap.ker (ccm15_relativeDual Y B k).g.hom) :
    (w.1 : Module.Dual ℚ (((relativeChainFunctor ℚ).obj (TopPair.ofSubset Bᶜ)).X k)).comp
      (((relativeChainFunctor ℚ).obj (TopPair.ofSubset Bᶜ)).d i k).hom = 0 := by
  by_cases hrel : (ComplexShape.down ℕ).Rel i k
  · obtain rfl := (ComplexShape.down ℕ).prev_eq' hrel
    exact w.2
  · rw [HomologicalComplex.shape _ _ _ hrel, ModuleCat.hom_zero, LinearMap.comp_zero]

/-- The absolute lift of a relative cocycle is a cocycle. -/
private theorem hc9kc_coboundary_cocycle (Y : TopCat.{0}) (B : Set Y) (k : ℕ)
    (w : LinearMap.ker (ccm15_relativeDual Y B k).g.hom) :
    coboundary ℚ k (relativeCochainToAbsolute ℚ (TopPair.ofSubset Bᶜ) k w.1) = 0 := by
  ext c
  rw [coboundary_apply, relativeCochainToAbsolute_apply, ← relativeBoundary_projection]
  exact LinearMap.congr_fun (hc9kc_cocycle_comp_d Y B k (k + 1) w) _

/-- A representative of a relative cup differs from the Alexander--Whitney lift of the
factors by the coboundary of a cochain vanishing on both complements. -/
private theorem hc9kc_relativeCup_cochain (Y : TopCat.{0}) (S T : Closeds Y) (p q : ℕ)
    (u : LinearMap.ker (ccm15_relativeDual Y S p).g.hom)
    (v : LinearMap.ker (ccm15_relativeDual Y T q).g.hom)
    (r : LinearMap.ker (ccm15_relativeDual Y ((S ⊓ T : Closeds Y) : Set Y) (p + q)).g.hom)
    (hr : hc9kc_dualClass ((relativeChainFunctor ℚ).obj
        (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ)) (p + q) r =
      ccm15_relativeCup Y S T p q
        (hc9kc_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (S : Set Y)ᶜ)) p u)
        (hc9kc_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (T : Set Y)ᶜ)) q v)) :
    ∃ e : Module.Dual ℚ (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X
        ((ComplexShape.down ℕ).next (p + q))),
      (∀ σ (b : Bool), (∀ t, Y.toSSetObjEquiv _ σ t ∈ ccm13_complementFamily Y S T b) →
        e (chainOfSimplex ℚ σ) = 0) ∧
      relativeCochainToAbsolute ℚ _ (p + q) r.1 =
        ccm13_relativeCupLift Y S T p q u.1 v.1 +
          e.comp (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d (p + q)
            ((ComplexShape.down ℕ).next (p + q))).hom := by
  let n := p + q
  let Qs := ccm14_smallRelativeComplex Y S T
  let proj := ccm14_smallProjection Y S T
  have h1 := hr.trans (hc9kc_relativeCup_class Y S T p q u v)
  have hA := hc9kc_dualClass_naturality (ccm14_relativeComparison Y S T) n r
  have hB := hc9kc_comparison_transport Y S T n
    ((ccm15_smallDual Y S T n).moduleCatHomologyClass (ccm15_cycleCup Y S T p q u v))
  have h2 := hA.symm.trans ((congrArg (HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap (ccm14_relativeComparison Y S T)) n) h1).trans hB)
  have h3 := (hc9kc_dualEquiv Qs n).injective h2
  have hinj : Function.Injective ((Qs.sc n).linearDual.moduleCatHomologyIso.inv.hom) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have h4 := (Submodule.Quotient.eq _).mp (hinj h3)
  obtain ⟨e', he0⟩ := h4
  let e0 : Module.Dual ℚ (Qs.X ((ComplexShape.down ℕ).next n)) := e'
  refine ⟨e0.comp (proj.f ((ComplexShape.down ℕ).next n)).hom, ?_, ?_⟩
  · intro σ b hσ
    change e0 ((proj.f _).hom (chainOfSimplex ℚ σ)) = 0
    rw [hc9kc_smallProjection_simplex_zero Y S T σ b hσ, map_zero]
  · ext y
    have hv := congrArg (fun z => (z.1 : Module.Dual ℚ (Qs.X n)) ((proj.f n).hom y)) he0
    simp only [Submodule.coe_sub] at hv
    have hcomp := ConcreteCategory.congr_hom (congrArg (fun g => g.f n)
      (cokernel.π_desc _ (relativeChainProjection ℚ
        (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ))
        _ : ccm14_smallProjection Y S T ≫ ccm14_relativeComparison Y S T = _)) y
    have hcup := LinearMap.congr_fun (ccm15_smallCup_projection Y S T p q u.1 v.1) y
    have hd := ConcreteCategory.congr_hom (proj.comm n ((ComplexShape.down ℕ).next n)) y
    change (relativeCochainToAbsolute ℚ _ n r.1) y =
      ccm13_relativeCupLift Y S T p q u.1 v.1 y +
        e0 ((proj.f _).hom ((((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d n
          ((ComplexShape.down ℕ).next n)).hom y))
    change (Qs.d n _).hom ((proj.f n).hom y) = (proj.f _).hom
      ((((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d n _).hom y) at hd
    rw [← hd, ← hcup]
    let r1 : Module.Dual ℚ (((relativeChainFunctor ℚ).obj
      (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ)).X n) := r.1
    change r1 (((relativeChainProjection ℚ _).f n).hom y) = _
    have hc' : r1 (((ccm14_relativeComparison Y S T).f n).hom ((proj.f n).hom y)) =
        r1 (((relativeChainProjection ℚ _).f n).hom y) := congrArg r1 hcomp
    change e0 ((Qs.d n _).hom ((proj.f n).hom y)) =
      r1 (((ccm14_relativeComparison Y S T).f n).hom ((proj.f n).hom y)) -
        ccm14_smallRelativeCup Y S T p q u.1 v.1 ((proj.f n).hom y) at hv
    rw [hv, hc']
    change _ = ccm14_smallRelativeCup Y S T p q u.1 v.1 ((proj.f n).hom y) + _
    ring

open scoped Simplicial in
/-- A cup with the coboundary of a cochain in the first slot vanishes on a chain whose
boundary is small, when each cover member kills one of the two factors. -/
private theorem hc9kc_cup_coboundary_left_zero (Y : TopCat.{0}) {ι : Type}
    (F : ι → Set Y) (n j k : ℕ)
    (e : Module.Dual ℚ (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X j))
    (w : Cochain ℚ (TopCat.toSSet.obj Y) k) (hw : coboundary ℚ k w = 0)
    (hF : ∀ i, (∀ σ : (TopCat.toSSet.obj Y) _⦋j⦌, (∀ t, Y.toSSetObjEquiv _ σ t ∈ F i) →
        e (chainOfSimplex ℚ σ) = 0) ∨
      (∀ σ : (TopCat.toSSet.obj Y) _⦋k⦌, (∀ t, Y.toSSetObjEquiv _ σ t ∈ F i) →
        w (chainOfSimplex ℚ σ) = 0))
    (x : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X (n + k))
    (hx : ∀ m, (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d (n + k) m).hom x ∈
      hc9kc_smallSpan Y F m) :
    cupCochain Y n k
      (e.comp (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d n j).hom) w x = 0 := by
  let C := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)
  by_cases hrel : (ComplexShape.down ℕ).Rel n j
  · have hn : n = j + 1 := hrel.symm
    subst hn
    change cupCochain Y (j + 1) k (coboundary ℚ j e) w x = 0
    have hL := coboundary_cupCochain Y j k e w
    rw [hw, map_zero, smul_zero, add_zero] at hL
    let y := (C.XIsoOfEq (by omega : j + k + 1 = j + 1 + k)).inv.hom x
    have hxy : x = reassocChain ℚ j k y := by
      change x = (C.XIsoOfEq _).hom.hom ((C.XIsoOfEq _).inv.hom x)
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.inv_hom_id]
      rfl
    rw [hxy, ← LinearMap.comp_apply, ← hL, coboundary_apply]
    have hmem : boundary ℚ (j + k) y ∈ hc9kc_smallSpan Y F (j + k) := by
      have h1 := hx (j + k)
      rw [hxy] at h1
      change (C.d (j + 1 + k) (j + k)).hom ((C.XIsoOfEq _).hom.hom y) ∈ _ at h1
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
        HomologicalComplex.XIsoOfEq_hom_comp_d] at h1
      exact h1
    apply hc9kc_smallSpan_le_ker Y F (j + k) (cupCochain Y j k e w) _ hmem
    intro σ i hσ
    rw [cupCochain_apply_simplex]
    rcases hF i with h | h
    · rw [h _ (hc9kc_frontFace_mem Y σ (F i) hσ), zero_mul]
    · rw [h _ (hc9kc_backFace_mem Y σ (F i) hσ), mul_zero]
  · rw [C.shape n j hrel, ModuleCat.hom_zero, LinearMap.comp_zero, map_zero,
      LinearMap.zero_apply, LinearMap.zero_apply]

open scoped Simplicial in
/-- A cup with the coboundary of a cochain in the second slot vanishes on a chain whose
boundary is small, when each cover member kills one of the two factors. -/
private theorem hc9kc_cup_coboundary_right_zero (Y : TopCat.{0}) {ι : Type}
    (F : ι → Set Y) (a n j : ℕ)
    (u : Cochain ℚ (TopCat.toSSet.obj Y) a) (hu : coboundary ℚ a u = 0)
    (f : Module.Dual ℚ (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X j))
    (hF : ∀ i, (∀ σ : (TopCat.toSSet.obj Y) _⦋a⦌, (∀ t, Y.toSSetObjEquiv _ σ t ∈ F i) →
        u (chainOfSimplex ℚ σ) = 0) ∨
      (∀ σ : (TopCat.toSSet.obj Y) _⦋j⦌, (∀ t, Y.toSSetObjEquiv _ σ t ∈ F i) →
        f (chainOfSimplex ℚ σ) = 0))
    (x : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X (a + n))
    (hx : ∀ m, (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d (a + n) m).hom x ∈
      hc9kc_smallSpan Y F m) :
    cupCochain Y a n u
      (f.comp (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d n j).hom) x = 0 := by
  let C := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)
  by_cases hrel : (ComplexShape.down ℕ).Rel n j
  · have hn : n = j + 1 := hrel.symm
    subst hn
    change cupCochain Y a (j + 1) u (coboundary ℚ j f) x = 0
    have hL := coboundary_cupCochain Y a j u f
    rw [hu, map_zero, LinearMap.zero_apply, LinearMap.zero_comp, zero_add] at hL
    have hv := LinearMap.congr_fun hL x
    rw [coboundary_apply, LinearMap.smul_apply, smul_eq_mul] at hv
    have hmem : boundary ℚ (a + j) x ∈ hc9kc_smallSpan Y F (a + j) := hx (a + j)
    have h0 : cupCochain Y a j u f (boundary ℚ (a + j) x) = 0 := by
      apply hc9kc_smallSpan_le_ker Y F (a + j) (cupCochain Y a j u f) _ hmem
      intro σ i hσ
      rw [cupCochain_apply_simplex]
      rcases hF i with h | h
      · rw [h _ (hc9kc_frontFace_mem Y σ (F i) hσ), zero_mul]
      · rw [h _ (hc9kc_backFace_mem Y σ (F i) hσ), mul_zero]
    rw [h0] at hv
    exact (mul_eq_zero.mp hv.symm).resolve_left (pow_ne_zero _ (by norm_num))
  · rw [C.shape n j hrel, ModuleCat.hom_zero, LinearMap.comp_zero, map_zero,
      LinearMap.zero_apply]

/-! ## Associativity of the relative cup -/

/-- Transport of a relative class along an equality of degrees.
Source: equality of degrees in `RelativeCohomology`. -/
def hc9kc_cast {P : TopPair.{0}} {m n : ℕ} (h : m = n) (u : RelativeCohomology ℚ P m) :
    RelativeCohomology ℚ P n :=
  h ▸ u

/-- Transport along `rfl` is the identity. -/
example (u : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of PUnit) Set.univ) 0) :
    hc9kc_cast rfl u = u := rfl

/-- The identity map of pairs enlarging the support from `A` to `B`.
Source: Hatcher, Algebraic Topology, §3.2, naturality of relative cohomology in the pair. -/
def hc9kc_supportMap (Y : TopCat.{0}) (A B : Set Y) (h : A ⊆ B) :
    TopPair.ofSubset (X := Y) Bᶜ ⟶ TopPair.ofSubset (X := Y) Aᶜ :=
  TopPair.ofSubsetHom (𝟙 Y) (fun _ hy hA => hy (h hA))

/-- Enlarging the empty support on a point. -/
example : TopPair.ofSubset (X := TopCat.of PUnit) (Set.univ : Set PUnit)ᶜ ⟶
    TopPair.ofSubset (X := TopCat.of PUnit) (∅ : Set PUnit)ᶜ :=
  hc9kc_supportMap (TopCat.of PUnit) ∅ Set.univ (Set.empty_subset _)

private theorem hc9kc_chainClass_congr (P : TopPair.{0}) (n : ℕ)
    (c c' : ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).X n)
    (hc : (((relativeChainFunctor ℚ).obj P).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ P).f n).hom c) = 0)
    (hc' : (((relativeChainFunctor ℚ).obj P).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ P).f n).hom c') = 0)
    (h : c = c') :
    hc9kc_chainClass P n c hc = hc9kc_chainClass P n c' hc' := by
  subst h
  rfl

private theorem hc9kc_chainClass_supportMap (Y : TopCat.{0}) (A B : Set Y) (h : A ⊆ B)
    (n : ℕ) (x : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X n)
    (hx : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := Y) Bᶜ)).d n
        ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ (TopPair.ofSubset (X := Y) Bᶜ)).f n).hom x) = 0)
    (hx' : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := Y) Aᶜ)).d n
        ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ (TopPair.ofSubset (X := Y) Aᶜ)).f n).hom x) = 0) :
    relativeHomologyMap ℚ n (hc9kc_supportMap Y A B h) (hc9kc_chainClass _ n x hx) =
      hc9kc_chainClass _ n x hx' := by
  unfold hc9kc_chainClass
  refine (ShortComplex.moduleCatHomologyClass_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) n).map
      ((relativeChainFunctor ℚ).map (hc9kc_supportMap Y A B h))) _).trans ?_
  congr 1
  apply Subtype.ext
  have hn := ConcreteCategory.congr_hom (congrArg (fun g => g.f n)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
      (hc9kc_supportMap Y A B h))) x
  have hid : TopPair.Hom.fst (hc9kc_supportMap Y A B h) = 𝟙 Y := rfl
  rw [hid] at hn
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  exact hn

private theorem hc9kc_chainClass_cast (P : TopPair.{0}) {m n : ℕ} (h : m = n)
    (x : ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).X m)
    (hx : (((relativeChainFunctor ℚ).obj P).d m ((ComplexShape.down ℕ).next m)).hom
      (((relativeChainProjection ℚ P).f m).hom x) = 0)
    (hx' : (((relativeChainFunctor ℚ).obj P).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ P).f n).hom
        ((((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).XIsoOfEq h).hom.hom x))
          = 0) :
    h ▸ hc9kc_chainClass P m x hx = hc9kc_chainClass P n
      ((((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).XIsoOfEq h).hom.hom x)
        hx' := by
  subst h
  apply hc9kc_chainClass_congr
  rw [HomologicalComplex.XIsoOfEq_rfl]
  rfl

private theorem hc9kc_pairing_degree_cast {P : TopPair.{0}} {m n : ℕ}
    (h : m = n) (u : RelativeCohomology ℚ P n) (z : RelativeHomology ℚ P m) :
    relativeCohomologyEquivDualHomology ℚ P m (h.symm ▸ u) z =
      relativeCohomologyEquivDualHomology ℚ P n u (h ▸ z) := by
  subst n
  rfl

private theorem hc9kc_pairing_cast_chainClass {P : TopPair.{0}} {m n : ℕ}
    (h : m = n) (u : RelativeCohomology ℚ P n)
    (x : ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).X m)
    (hx : (((relativeChainFunctor ℚ).obj P).d m ((ComplexShape.down ℕ).next m)).hom
      (((relativeChainProjection ℚ P).f m).hom x) = 0)
    (hx' : (((relativeChainFunctor ℚ).obj P).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ P).f n).hom
        ((((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).XIsoOfEq h).hom.hom x))
          = 0) :
    relativeCohomologyEquivDualHomology ℚ P m (hc9kc_cast h.symm u) (hc9kc_chainClass P m x hx) =
      relativeCohomologyEquivDualHomology ℚ P n u (hc9kc_chainClass P n
        ((((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).XIsoOfEq h).hom.hom x)
          hx') := by
  subst h
  congr 1

private theorem hc9kc_small_all (Y : TopCat.{0}) {ι : Type} (F : ι → Set Y) (N : ℕ)
    (x : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X N)
    (hx : (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d N
      ((ComplexShape.down ℕ).next N)).hom x ∈ hc9kc_smallSpan Y F ((ComplexShape.down ℕ).next N)) :
    ∀ m, (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d N m).hom x ∈
      hc9kc_smallSpan Y F m := by
  intro m
  by_cases hrel : (ComplexShape.down ℕ).Rel N m
  · obtain rfl := (ComplexShape.down ℕ).next_eq' hrel
    exact hx
  · rw [HomologicalComplex.shape _ _ _ hrel, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _

private theorem hc9kc_small_cast (Y : TopCat.{0}) {ι : Type} (F : ι → Set Y) {N N' : ℕ}
    (h : N = N') (x : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X N)
    (hx : ∀ m, (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d N m).hom x ∈
      hc9kc_smallSpan Y F m) :
    ∀ m, (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d N' m).hom
      ((((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).XIsoOfEq h).hom.hom x) ∈
        hc9kc_smallSpan Y F m := by
  subst h
  intro m
  rw [HomologicalComplex.XIsoOfEq_rfl]
  exact hx m

private theorem hc9kc_small_cycle (Y : TopCat.{0}) (S T : Set Y) {ι : Type}
    (F : ι → Set Y) (hF : ∀ i, ∃ b, F i ⊆ ccm13_complementFamily Y S T b) (N : ℕ)
    (x : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X N)
    (hx : ∀ m, (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d N m).hom x ∈
      hc9kc_smallSpan Y F m) :
    ((ccm14_smallRelativeComplex Y S T).d N ((ComplexShape.down ℕ).next N)).hom
      (((ccm14_smallProjection Y S T).f N).hom x) = 0 := by
  have hd := ConcreteCategory.congr_hom
    ((ccm14_smallProjection Y S T).comm N ((ComplexShape.down ℕ).next N)) x
  change ((ccm14_smallRelativeComplex Y S T).d N _).hom
      (((ccm14_smallProjection Y S T).f N).hom x) =
    ((ccm14_smallProjection Y S T).f _).hom
      ((((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d N _).hom x) at hd
  rw [hd]
  refine hc9kc_smallSpan_le_ker Y F _ ((ccm14_smallProjection Y S T).f _).hom
    (fun σ i hσ => ?_) (hx _)
  obtain ⟨b, hb⟩ := hF i
  exact hc9kc_smallProjection_simplex_zero Y S T σ b (fun t => hb (hσ t))

open scoped Simplicial in
/-- Associativity of the relative cup, with the supports and degrees reassociated.
Source: Hatcher, *Algebraic Topology*, §3.2, associativity of relative cup products. -/
theorem hc9kc_relativeCup_assoc (Y : TopCat.{0}) (S T W : Closeds Y) (a b c : ℕ)
    (U : RelativeCohomology ℚ (TopPair.ofSubset (S : Set Y)ᶜ) a)
    (V : RelativeCohomology ℚ (TopPair.ofSubset (T : Set Y)ᶜ) b)
    (X : RelativeCohomology ℚ (TopPair.ofSubset (W : Set Y)ᶜ) c) :
    relativeCohomologyMap ℚ (a + b + c)
      (hc9kc_supportMap Y ((S ⊓ T ⊓ W : Closeds Y) : Set Y) ((S ⊓ (T ⊓ W) : Closeds Y) : Set Y)
        (fun y hy => by
          simp only [Closeds.coe_inf, Set.mem_inter_iff] at hy ⊢
          tauto))
      (ccm15_relativeCup Y (S ⊓ T) W (a + b) c (ccm15_relativeCup Y S T a b U V) X) =
    hc9kc_cast (Nat.add_assoc a b c).symm
      (ccm15_relativeCup Y S (T ⊓ W) a (b + c) U (ccm15_relativeCup Y T W b c V X)) := by
  obtain ⟨u, rfl⟩ := hc9kc_dualClass_surjective _ a U
  obtain ⟨v, rfl⟩ := hc9kc_dualClass_surjective _ b V
  obtain ⟨w, rfl⟩ := hc9kc_dualClass_surjective _ c X
  obtain ⟨r, hr⟩ := hc9kc_dualClass_surjective _ (a + b)
    (ccm15_relativeCup Y S T a b (hc9kc_dualClass _ a u) (hc9kc_dualClass _ b v))
  obtain ⟨s, hs⟩ := hc9kc_dualClass_surjective _ (b + c)
    (ccm15_relativeCup Y T W b c (hc9kc_dualClass _ b v) (hc9kc_dualClass _ c w))
  obtain ⟨e, he, hre⟩ := hc9kc_relativeCup_cochain Y S T a b u v r hr
  obtain ⟨f, hf, hsf⟩ := hc9kc_relativeCup_cochain Y T W b c v w s hs
  rw [← hr, ← hs]
  apply (relativeCohomologyEquivDualHomology ℚ _ (a + b + c)).injective
  apply LinearMap.ext
  intro h
  let F : Fin 3 → Set Y := ![(S : Set Y)ᶜ, (T : Set Y)ᶜ, (W : Set Y)ᶜ]
  have hopen : ∀ i, IsOpen (F i) := by
    intro i
    fin_cases i
    · exact S.isClosed.isOpen_compl
    · exact T.isClosed.isOpen_compl
    · exact W.isClosed.isOpen_compl
  have hcover : ⋃ i, F i = ((S ⊓ (T ⊓ W) : Closeds Y) : Set Y)ᶜ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_compl_iff, Closeds.coe_inf, Set.mem_inter_iff,
      not_and_or, Fin.exists_fin_succ, Fin.exists_fin_zero, F, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two]
    tauto
  obtain ⟨x, hx, rfl, hsmall⟩ := hc9kc_exists_small_representative Y _ F hopen hcover
    (a + b + c) h
  have hsm := hc9kc_small_all Y F _ x hsmall
  -- the left side
  have hFL : ∀ i, ∃ bb, F i ⊆ ccm13_complementFamily Y
      ((S ⊓ T : Closeds Y) : Set Y) (W : Set Y) bb := by
    intro i
    fin_cases i
    · exact ⟨false, fun y hy hST => hy hST.1⟩
    · exact ⟨false, fun y hy hST => hy hST.2⟩
    · exact ⟨true, fun y hy => hy⟩
  have hxL := hc9kc_small_cycle Y _ _ F hFL _ x hsm
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    hc9kc_chainClass_supportMap Y _ _ _ _ x hx
      (hc9kc_relativeCycle_of_small Y (S ⊓ T) W _ x hxL),
    hc9kc_relativeCup_eval Y (S ⊓ T) W (a + b) c r w x hxL]
  -- the right side
  have hFR : ∀ i, ∃ bb, F i ⊆ ccm13_complementFamily Y (S : Set Y)
      ((T ⊓ W : Closeds Y) : Set Y) bb := by
    intro i
    fin_cases i
    · exact ⟨false, fun y hy => hy⟩
    · exact ⟨true, fun y hy hTW => hy hTW.1⟩
    · exact ⟨true, fun y hy hTW => hy hTW.2⟩
  let x' := (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).XIsoOfEq
    (Nat.add_assoc a b c)).hom.hom x
  have hsm' := hc9kc_small_cast Y F (Nat.add_assoc a b c) x hsm
  have hxR := hc9kc_small_cycle Y _ _ F hFR _ x' hsm'
  refine Eq.trans ?_ (hc9kc_pairing_cast_chainClass
    (P := TopPair.ofSubset (X := Y) ((S ⊓ (T ⊓ W) : Closeds Y) : Set Y)ᶜ)
    (Nat.add_assoc a b c) _ x hx (hc9kc_relativeCycle_of_small Y S (T ⊓ W) _ x' hxR)).symm
  refine Eq.trans ?_ (hc9kc_relativeCup_eval Y S (T ⊓ W) a (b + c) u s x' hxR).symm
  unfold ccm13_relativeCupLift
  rw [hre, hsf, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply]
  have hFe : ∀ i, (∀ σ : (TopCat.toSSet.obj Y) _⦋(ComplexShape.down ℕ).next (a + b)⦌,
      (∀ t, Y.toSSetObjEquiv _ σ t ∈ F i) → e (chainOfSimplex ℚ σ) = 0) ∨
      (∀ σ : (TopCat.toSSet.obj Y) _⦋c⦌, (∀ t, Y.toSSetObjEquiv _ σ t ∈ F i) →
        relativeCochainToAbsolute ℚ (TopPair.ofSubset (W : Set Y)ᶜ) c w.1
          (chainOfSimplex ℚ σ) = 0) := by
    intro i
    fin_cases i
    · exact Or.inl fun σ hσ => he σ false hσ
    · exact Or.inl fun σ hσ => he σ true hσ
    · exact Or.inr fun σ hσ => hc9kc_relativeCochain_simplex_zero Y _ c w.1 σ hσ
  have hFf : ∀ i, (∀ σ : (TopCat.toSSet.obj Y) _⦋a⦌, (∀ t, Y.toSSetObjEquiv _ σ t ∈ F i) →
        relativeCochainToAbsolute ℚ (TopPair.ofSubset (S : Set Y)ᶜ) a u.1
          (chainOfSimplex ℚ σ) = 0) ∨
      (∀ σ : (TopCat.toSSet.obj Y) _⦋(ComplexShape.down ℕ).next (b + c)⦌,
      (∀ t, Y.toSSetObjEquiv _ σ t ∈ F i) → f (chainOfSimplex ℚ σ) = 0) := by
    intro i
    fin_cases i
    · exact Or.inl fun σ hσ => hc9kc_relativeCochain_simplex_zero Y _ a u.1 σ hσ
    · exact Or.inr fun σ hσ => hf σ false hσ
    · exact Or.inr fun σ hσ => hf σ true hσ
  change _ = cupCochain Y a (b + c) (relativeCochainToAbsolute ℚ _ a u.1)
      (ccm13_relativeCupLift Y T W b c v.1 w.1) x' +
    cupCochain Y a (b + c) (relativeCochainToAbsolute ℚ _ a u.1)
      (f.comp (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d (b + c)
        ((ComplexShape.down ℕ).next (b + c))).hom) x'
  rw [hc9kc_cup_coboundary_left_zero Y F (a + b) _ c e _ (hc9kc_coboundary_cocycle Y W c w)
      hFe x hsm, add_zero,
    hc9kc_cup_coboundary_right_zero Y F a (b + c) _ _ (hc9kc_coboundary_cocycle Y S a u) f
      hFf x' hsm', add_zero]
  unfold ccm13_relativeCupLift
  rw [cupCochain_assoc]
  rfl

/-! ## Transport along equal supports and degrees -/

/-- Transport of a relative class along equalities of closed supports and of degrees.
Source: equality of supports in `TopPair.ofSubset`; equality of degrees in
`RelativeCohomology`. -/
def hc9kc_transport {Y : TopCat.{0}} {A B : Closeds Y} (hAB : A = B) {m n : ℕ} (hmn : m = n)
    (U : RelativeCohomology ℚ (TopPair.ofSubset (A : Set Y)ᶜ) m) :
    RelativeCohomology ℚ (TopPair.ofSubset (B : Set Y)ᶜ) n := by
  subst hAB
  subst hmn
  exact U

/-- Transport along reflexivity is the identity. -/
example (U : RelativeCohomology ℚ
    (TopPair.ofSubset (X := TopCat.of PUnit) ((⊤ : Closeds PUnit) : Set PUnit)ᶜ) 0) :
    hc9kc_transport rfl rfl U = U := rfl

private theorem hc9kc_transport_rfl {Y : TopCat.{0}} {A : Closeds Y} {m : ℕ}
    (U : RelativeCohomology ℚ (TopPair.ofSubset (A : Set Y)ᶜ) m) :
    hc9kc_transport rfl rfl U = U := rfl

private theorem hc9kc_transport_trans {Y : TopCat.{0}} {A B C : Closeds Y}
    (h₁ : A = B) (h₂ : B = C) {m n k : ℕ} (k₁ : m = n) (k₂ : n = k)
    (U : RelativeCohomology ℚ (TopPair.ofSubset (A : Set Y)ᶜ) m) :
    hc9kc_transport h₂ k₂ (hc9kc_transport h₁ k₁ U) = hc9kc_transport (h₁.trans h₂) (k₁.trans k₂) U := by
  subst h₁ h₂ k₁ k₂
  rfl

private theorem hc9kc_transport_eq_iff {Y : TopCat.{0}} {A B : Closeds Y}
    (h : A = B) {m n : ℕ} (k : m = n)
    (U : RelativeCohomology ℚ (TopPair.ofSubset (A : Set Y)ᶜ) m)
    (V : RelativeCohomology ℚ (TopPair.ofSubset (B : Set Y)ᶜ) n) :
    hc9kc_transport h k U = V ↔ U = hc9kc_transport h.symm k.symm V := by
  subst h k
  rfl

private theorem hc9kc_relativeCup_transport (Y : TopCat.{0}) {S S' T T' : Closeds Y}
    (hS : S = S') (hT : T = T') {p p' q q' : ℕ} (kp : p = p') (kq : q = q')
    (U : RelativeCohomology ℚ (TopPair.ofSubset (S : Set Y)ᶜ) p)
    (V : RelativeCohomology ℚ (TopPair.ofSubset (T : Set Y)ᶜ) q) :
    ccm15_relativeCup Y S' T' p' q' (hc9kc_transport hS kp U) (hc9kc_transport hT kq V) =
      hc9kc_transport (by rw [hS, hT]) (by rw [kp, kq]) (ccm15_relativeCup Y S T p q U V) := by
  subst hS hT kp kq
  rfl

private theorem hc9kc_supportMap_transport (Y : TopCat.{0}) {A B : Closeds Y} (h : A = B)
    (hsub : (A : Set Y) ⊆ B) {m : ℕ}
    (U : RelativeCohomology ℚ (TopPair.ofSubset (A : Set Y)ᶜ) m) :
    relativeCohomologyMap ℚ m (hc9kc_supportMap Y A B hsub) U = hc9kc_transport h rfl U := by
  subst h
  have h1 : hc9kc_supportMap Y A A hsub = 𝟙 _ := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext a
      rfl
    · ext x
      rfl
  rw [h1, relativeCohomologyMap_id]
  rfl

private theorem hc9kc_cast_transport {Y : TopCat.{0}} {A : Closeds Y} {m n : ℕ} (k : m = n)
    (U : RelativeCohomology ℚ (TopPair.ofSubset (A : Set Y)ᶜ) m) :
    hc9kc_cast k U = hc9kc_transport rfl k U := by
  subst k
  rfl

/-- Two maps of pairs with the same underlying map, from complements of equal supports. -/
private theorem hc9kc_transport_pullback (Y Z : TopCat.{0}) {A B : Closeds Y} (h : A = B)
    {C : Set Z} (f g : Y ⟶ Z) (hfg : f = g) (hf : ∀ a ∈ (A : Set Y)ᶜ, f a ∈ C)
    (hg : ∀ a ∈ (B : Set Y)ᶜ, g a ∈ C) {m : ℕ}
    (U : RelativeCohomology ℚ (TopPair.ofSubset C) m) :
    hc9kc_transport h rfl (relativeCohomologyMap ℚ m (TopPair.ofSubsetHom f hf) U) =
      relativeCohomologyMap ℚ m (TopPair.ofSubsetHom g hg) U := by
  subst h hfg
  rfl

private theorem hc9kc_transport_relativeCohomologyMap {P : TopPair.{0}} (Y : TopCat.{0})
    {A : Closeds Y} (φ : TopPair.ofSubset (X := Y) (A : Set Y)ᶜ ⟶ P) {m n : ℕ} (k : m = n)
    (U : RelativeCohomology ℚ P m) :
    relativeCohomologyMap ℚ n φ (k ▸ U) = hc9kc_transport rfl k (relativeCohomologyMap ℚ m φ U) := by
  subst k
  rfl

private theorem hc9kc_relativeCohomologyMap_transport (Y Z : TopCat.{0}) {A : Closeds Z}
    {B : Closeds Y} (φ : TopPair.ofSubset (X := Y) (B : Set Y)ᶜ ⟶
      TopPair.ofSubset (X := Z) (A : Set Z)ᶜ) {m n : ℕ} (k : m = n)
    (U : RelativeCohomology ℚ (TopPair.ofSubset (A : Set Z)ᶜ) m) :
    relativeCohomologyMap ℚ n φ (hc9kc_transport rfl k U) =
      hc9kc_transport rfl k (relativeCohomologyMap ℚ m φ U) := by
  subst k
  rfl

private theorem hc9kc_eqRec_transport {Y : TopCat.{0}} {A : Closeds Y} {m n : ℕ} (k k' : m = n)
    (U : RelativeCohomology ℚ (TopPair.ofSubset (A : Set Y)ᶜ) m) :
    (k ▸ U : RelativeCohomology ℚ (TopPair.ofSubset (A : Set Y)ᶜ) n) = hc9kc_transport rfl k' U := by
  subst k
  rfl

/-- Equal normal-coordinate maps have the same normal class up to the equality of supports. -/
private theorem hc9kc_normalClass_congr (Y : TopCat.{0}) (c : ℕ) {f g : C(Y, Fin c → ℂ)}
    (h : f = g) :
    ccm17_normalClass Y c g =
      hc9kc_transport (congrArg (ccm17_zeroSupport Y c) h) rfl (ccm17_normalClass Y c f) := by
  subst h
  rfl

/-- Reindexing normal coordinates along an equality of their number. -/
private def hc9kc_reindex {Y : TopCat.{0}} {m n : ℕ} (e : m = n) (g : C(Y, Fin n → ℂ)) :
    C(Y, Fin m → ℂ) :=
  ⟨fun y i => g y (Fin.cast e i), by fun_prop⟩

private theorem hc9kc_zeroSupport_reindex (Y : TopCat.{0}) {m n : ℕ} (e : m = n)
    (g : C(Y, Fin n → ℂ)) :
    ccm17_zeroSupport Y n g = ccm17_zeroSupport Y m (hc9kc_reindex e g) := by
  subst e
  rfl

private theorem hc9kc_normalClass_reindex (Y : TopCat.{0}) {m n : ℕ} (e : m = n)
    (g : C(Y, Fin n → ℂ)) :
    ccm17_normalClass Y m (hc9kc_reindex e g) =
      hc9kc_transport (hc9kc_zeroSupport_reindex Y e g) (by rw [e])
        (ccm17_normalClass Y n g) := by
  subst e
  rfl

/-- Associativity in transport form. -/
private theorem hc9kc_relativeCup_assoc' (Y : TopCat.{0}) (S T W : Closeds Y) (a b c : ℕ)
    (U : RelativeCohomology ℚ (TopPair.ofSubset (S : Set Y)ᶜ) a)
    (V : RelativeCohomology ℚ (TopPair.ofSubset (T : Set Y)ᶜ) b)
    (X : RelativeCohomology ℚ (TopPair.ofSubset (W : Set Y)ᶜ) c) :
    ccm15_relativeCup Y (S ⊓ T) W (a + b) c (ccm15_relativeCup Y S T a b U V) X =
      hc9kc_transport (inf_assoc S T W).symm (Nat.add_assoc a b c).symm
        (ccm15_relativeCup Y S (T ⊓ W) a (b + c) U (ccm15_relativeCup Y T W b c V X)) := by
  have h := hc9kc_relativeCup_assoc Y S T W a b c U V X
  rw [hc9kc_supportMap_transport Y (inf_assoc S T W), hc9kc_cast_transport,
    hc9kc_transport_eq_iff, hc9kc_transport_trans] at h
  exact h

/-- Zero support of a pullback is the preimage of the zero support. -/
private theorem hc9kc_normalClass_comp (Y Z : TopCat.{0}) (c : ℕ)
    (f : C(Y, Z)) (g : C(Z, Fin c → ℂ)) :
    ccm17_normalClass Y c (g.comp f) =
      relativeCohomologyMap ℚ (2 * c)
        (ccm17_preimagePair Y Z f (ccm17_zeroSupport Z c g))
        (ccm17_normalClass Z c g) := by
  unfold ccm17_normalClass
  change _ = ((relativeCohomologyMap ℚ (2 * c)
    (ccm17_preimagePair Y Z f (ccm17_zeroSupport Z c g))).comp
    (relativeCohomologyMap ℚ (2 * c) (ccm17_normalPair Z c g)))
      (normalizedPointCoclass c)
  rw [← relativeCohomologyMap_comp]
  rfl

/-! ## The divisor case on any space -/

/-- A first coordinate followed by the remaining normal coordinates. -/
private def hc9kc_cons {Y : TopCat.{0}} {n : ℕ} (x : C(Y, Fin 1 → ℂ)) (r : C(Y, Fin n → ℂ)) :
    C(Y, Fin (n + 1) → ℂ) :=
  ⟨fun y => Fin.cons (x y 0) (r y), by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      fun_prop
    · simp only [Fin.cons_succ]
      fun_prop⟩

private theorem hc9kc_zeroSupport_cons {Y : TopCat.{0}} {n : ℕ} (x : C(Y, Fin 1 → ℂ))
    (r : C(Y, Fin n → ℂ)) :
    ccm17_zeroSupport Y (n + 1) (hc9kc_cons x r) =
      ccm17_zeroSupport Y 1 x ⊓ ccm17_zeroSupport Y n r := by
  ext y
  change (Fin.cons (x y 0) (r y) : Fin (n + 1) → ℂ) = 0 ↔ x y = 0 ∧ r y = 0
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · have := congrFun h 0
      rw [Fin.cons_zero] at this
      rw [Fin.fin_one_eq_zero i]
      exact this
    · have := congrFun h i.succ
      rw [Fin.cons_succ] at this
      exact this
  · rintro ⟨h1, h2⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero]
      exact congrFun h1 0
    · rw [Fin.cons_succ]
      exact congrFun h2 j

/-- The divisor coordinate product, pulled back to any space. -/
private theorem hc9kc_divisor_product (Y : TopCat.{0}) (n : ℕ) (x : C(Y, Fin 1 → ℂ))
    (r : C(Y, Fin n → ℂ)) :
    ccm15_relativeCup Y (ccm17_zeroSupport Y 1 x) (ccm17_zeroSupport Y n r) 2 (2 * n)
        (ccm17_normalClass Y 1 x) (ccm17_normalClass Y n r) =
      hc9kc_transport (hc9kc_zeroSupport_cons x r) (by ring)
        (ccm17_normalClass Y (n + 1) (hc9kc_cons x r)) := by
  let E := TopCat.of (Fin (n + 1) → ℂ)
  let F : C(Y, E) := hc9kc_cons x r
  have hpb := ccm17_relativeCup_pullback Y E F (ccm17_zeroSupport E 1 (ccm17_head n))
    (ccm17_zeroSupport E n (ccm17_tail n)) 2 (2 * n)
    (ccm17_normalClass E 1 (ccm17_head n)) (ccm17_normalClass E n (ccm17_tail n))
  rw [ccm17_coordinate_product] at hpb
  have hx : (ccm17_head n).comp F = x := by
    ext y i
    rw [Fin.fin_one_eq_zero i]
    rfl
  have hr : (ccm17_tail n).comp F = r := by
    ext y i
    rfl
  have hZx : ccm17_zeroSupport Y 1 x =
      (ccm17_zeroSupport E 1 (ccm17_head n)).preimage F.continuous :=
    congrArg (ccm17_zeroSupport Y 1) hx.symm
  have hZr : ccm17_zeroSupport Y n r =
      (ccm17_zeroSupport E n (ccm17_tail n)).preimage F.continuous :=
    congrArg (ccm17_zeroSupport Y n) hr.symm
  have h1 : relativeCohomologyMap ℚ 2
      (ccm17_preimagePair Y E F (ccm17_zeroSupport E 1 (ccm17_head n)))
      (ccm17_normalClass E 1 (ccm17_head n)) =
      hc9kc_transport (B := (ccm17_zeroSupport E 1 (ccm17_head n)).preimage F.continuous)
        hZx (rfl : 2 * 1 = 2)
        (ccm17_normalClass Y 1 x) :=
    (hc9kc_normalClass_comp Y E 1 F (ccm17_head n)).symm.trans
      (hc9kc_normalClass_congr Y 1 hx.symm)
  have h2 : relativeCohomologyMap ℚ (2 * n)
      (ccm17_preimagePair Y E F (ccm17_zeroSupport E n (ccm17_tail n)))
      (ccm17_normalClass E n (ccm17_tail n)) =
      hc9kc_transport (B := (ccm17_zeroSupport E n (ccm17_tail n)).preimage F.continuous)
        hZr rfl
        (ccm17_normalClass Y n r) :=
    (hc9kc_normalClass_comp Y E n F (ccm17_tail n)).symm.trans
      (hc9kc_normalClass_congr Y n hr.symm)
  have hpb' : ccm15_relativeCup Y ((ccm17_zeroSupport E 1 (ccm17_head n)).preimage F.continuous)
      ((ccm17_zeroSupport E n (ccm17_tail n)).preimage F.continuous) 2 (2 * n)
      (hc9kc_transport hZx (rfl : 2 * 1 = 2) (ccm17_normalClass Y 1 x))
      (hc9kc_transport hZr rfl (ccm17_normalClass Y n r)) =
      relativeCohomologyMap ℚ (2 + 2 * n) (ccm17_preimagePair Y E F
        (ccm17_zeroSupport E 1 (ccm17_head n) ⊓ ccm17_zeroSupport E n (ccm17_tail n)))
          (ccm17_intersectionClass n) := by
    rw [← h1, ← h2]
    exact hpb.symm
  have hT := hc9kc_relativeCup_transport Y hZx hZr (rfl : 2 * 1 = 2) (rfl : 2 * n = 2 * n)
    (ccm17_normalClass Y 1 x) (ccm17_normalClass Y n r)
  have hI : ccm17_intersectionClass n = hc9kc_transport rfl (by ring)
      (relativeCohomologyMap ℚ (2 * (n + 1)) (ccm17_intersectionPair n)
        (normalizedPointCoclass (n + 1))) := by
    unfold ccm17_intersectionClass hc9kc_transport
    apply eq_of_heq
    simp only [eqRec_heq_iff, heq_eqRec_iff]
    rfl
  have hZ : ccm17_zeroSupport Y (n + 1) F =
      (ccm17_zeroSupport E 1 (ccm17_head n) ⊓ ccm17_zeroSupport E n (ccm17_tail n)).preimage
        F.continuous := by
    ext y
    change F y = 0 ↔ (ccm17_head n (F y) = 0 ∧ ccm17_tail n (F y) = 0)
    constructor
    · intro h
      rw [h]
      exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact congrFun h1 0
      · exact congrFun h2 j
  have hcomp : ccm17_preimagePair Y E F
      (ccm17_zeroSupport E 1 (ccm17_head n) ⊓ ccm17_zeroSupport E n (ccm17_tail n)) ≫
        ccm17_intersectionPair n =
      TopPair.ofSubsetHom (A := (((ccm17_zeroSupport E 1 (ccm17_head n) ⊓
          ccm17_zeroSupport E n (ccm17_tail n)).preimage F.continuous : Closeds Y) : Set Y)ᶜ)
        (B := ({0}ᶜ : Set (Fin (n + 1) → ℂ))) (TopCat.ofHom F)
        (fun a ha => show F a ∈ ({0}ᶜ : Set (Fin (n + 1) → ℂ)) from fun h0 => ha (by
        change F a = 0 at h0
        change ccm17_head n (F a) = 0 ∧ ccm17_tail n (F a) = 0
        rw [h0]
        exact ⟨rfl, rfl⟩)) := rfl
  have hJ : relativeCohomologyMap ℚ (2 + 2 * n) (ccm17_preimagePair Y E F
      (ccm17_zeroSupport E 1 (ccm17_head n) ⊓ ccm17_zeroSupport E n (ccm17_tail n)))
        (ccm17_intersectionClass n) =
      hc9kc_transport hZ (by ring) (ccm17_normalClass Y (n + 1) F) := by
    rw [hI, hc9kc_relativeCohomologyMap_transport, ← LinearMap.comp_apply,
      ← relativeCohomologyMap_comp, hcomp]
    unfold ccm17_normalClass ccm17_normalPair
    rw [← hc9kc_transport_pullback Y E hZ (TopCat.ofHom F) (TopCat.ofHom F) rfl
      (fun _ h => h), hc9kc_transport_trans]
  have hZ' : ccm17_zeroSupport Y (n + 1) F =
      (ccm17_zeroSupport E 1 (ccm17_head n)).preimage F.continuous ⊓
        (ccm17_zeroSupport E n (ccm17_tail n)).preimage F.continuous := hZ
  have hJ' : relativeCohomologyMap ℚ (2 + 2 * n) (ccm17_preimagePair Y E F
      (ccm17_zeroSupport E 1 (ccm17_head n) ⊓ ccm17_zeroSupport E n (ccm17_tail n)))
        (ccm17_intersectionClass n) =
      hc9kc_transport hZ' (by ring) (ccm17_normalClass Y (n + 1) F) := hJ
  have E1 := hT.symm.trans (hpb'.trans hJ')
  rw [hc9kc_transport_eq_iff, hc9kc_transport_trans] at E1
  exact E1

/-! ## The unit -/

private theorem hc9kc_absolute_pullback {P Q : TopPair.{0}} (f : P ⟶ Q)
    (n : ℕ) (u : RelativeCochain ℚ Q n) :
    relativeCochainToAbsolute ℚ P n
      (u.comp (((relativeChainFunctor ℚ).map f).f n).hom) =
    cochainMap ℚ (TopCat.toSSet.map (TopPair.Hom.fst f)) n
      (relativeCochainToAbsolute ℚ Q n u) := by
  ext c
  exact congrArg u (ConcreteCategory.congr_hom
    (congrArg (fun g => g.f n)
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)) c)

private theorem hc9kc_dualClass_chainClass (P : TopPair.{0}) (n : ℕ)
    (u : LinearMap.ker ((((relativeChainFunctor ℚ).obj P).sc n).linearDual.g.hom))
    (x : ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).X n)
    (hx : (((relativeChainFunctor ℚ).obj P).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ P).f n).hom x) = 0) :
    relativeCohomologyEquivDualHomology ℚ P n (hc9kc_dualClass _ n u)
        (hc9kc_chainClass P n x hx) =
      relativeCochainToAbsolute ℚ P n u.1 x :=
  hc9kc_dualClass_evaluation _ n u ⟨_, hx⟩

private theorem hc9kc_chainCycle_map {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ)
    (c : ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).X n)
    (hc : (((relativeChainFunctor ℚ).obj P).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ P).f n).hom c) = 0) :
    (((relativeChainFunctor ℚ).obj Q).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ Q).f n).hom
        (((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f))
          (ModuleCat.of ℚ ℚ)).f n).hom c)) = 0 := by
  have hp := ConcreteCategory.congr_hom
    (congrArg (fun g => g.f n)
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)) c
  change (((relativeChainFunctor ℚ).map f).f n).hom
      (((relativeChainProjection ℚ P).f n).hom c) =
    ((relativeChainProjection ℚ Q).f n).hom
      (((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f))
        (ModuleCat.of ℚ ℚ)).f n).hom c) at hp
  rw [← hp]
  have hcomm := ConcreteCategory.congr_hom
    (((relativeChainFunctor ℚ).map f).comm n ((ComplexShape.down ℕ).next n))
    (((relativeChainProjection ℚ P).f n).hom c)
  change (((relativeChainFunctor ℚ).obj Q).d n _).hom
      ((((relativeChainFunctor ℚ).map f).f n).hom _) =
    (((relativeChainFunctor ℚ).map f).f _).hom
      ((((relativeChainFunctor ℚ).obj P).d n _).hom _) at hcomm
  rw [hcomm, hc, map_zero]

private theorem hc9kc_chainClass_map {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ)
    (c : ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).X n)
    (hc : (((relativeChainFunctor ℚ).obj P).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ P).f n).hom c) = 0) :
    relativeHomologyMap ℚ n f (hc9kc_chainClass P n c hc) =
      hc9kc_chainClass Q n (((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f))
          (ModuleCat.of ℚ ℚ)).f n).hom c) (hc9kc_chainCycle_map f n c hc) := by
  unfold hc9kc_chainClass
  refine (ShortComplex.moduleCatHomologyClass_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) n).map
      ((relativeChainFunctor ℚ).map f)) _).trans ?_
  congr 1
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (congrArg (fun g => g.f n)
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)) c

private theorem hc9kc_standardLocalClass_eq_chainClass (d : ℕ)
    (hc : (((relativeChainFunctor ℚ).obj (puncturedPair ℝ d)).d d
      ((ComplexShape.down ℕ).next d)).hom
      (((relativeChainProjection ℚ (puncturedPair ℝ d)).f d).hom
        (chainOfSimplex ℚ (standardSingularSimplex d))) = 0) :
    standardLocalClass ℚ d =
      hc9kc_chainClass (puncturedPair ℝ d) d
        (chainOfSimplex ℚ (standardSingularSimplex d)) hc := by
  rw [hc9kc_chainClass_eq_homologyπ _ _ _ _ ((standardLocalCycle ℚ d).hom 1)]
  · rfl
  · change ((standardLocalCycle ℚ d ≫
      (standardLocalRelativeChainComplex ℚ d).iCycles d).hom) 1 = _
    rw [standardLocalCycle, HomologicalComplex.liftCycles_i]
    rfl

private theorem hc9kc_d_zero (K : ChainComplex (ModuleCat ℚ) ℕ) :
    K.d 0 ((ComplexShape.down ℕ).next 0) = 0 :=
  K.shape _ _ (fun h => Nat.succ_ne_zero _ h)

open scoped Simplicial in
/-- A representative of the normalized class of `(ℂ⁰, ∅)` is one on every vertex. -/
private theorem hc9kc_normalizedPointCoclass_zero_vertex
    (u : LinearMap.ker ((((relativeChainFunctor ℚ).obj (puncturedPair ℂ 0)).sc 0).linearDual.g.hom))
    (hu : hc9kc_dualClass _ 0 u = normalizedPointCoclass 0)
    (τ : (TopCat.toSSet.obj (TopCat.of (Fin 0 → ℂ))) _⦋0⦌) :
    relativeCochainToAbsolute ℚ (puncturedPair ℂ 0) 0 u.1 (chainOfSimplex ℚ τ) = 1 := by
  have h1 : relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ 0) 0
      (normalizedPointCoclass 0) (standardComplexLocalClass ℚ 0) = 1 := by
    change (relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ 0) (2 * 0))
      ((relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ 0) (2 * 0)).symm
        (normalizedDual (standardComplexLocalClass ℚ 0) _)) _ = 1
    rw [LinearEquiv.apply_symm_apply]
    exact Classical.choose_spec (Module.Projective.exists_dual_eq_one ℚ
      (standardComplexLocalClass_ne_zero_for_chart 0))
  have hstd : standardComplexLocalClass ℚ 0 =
      relativeHomologyMap ℚ 0 (standardComplexRealPairIso 0).inv (standardLocalClass ℚ 0) :=
    rfl
  have hc0 : (((relativeChainFunctor ℚ).obj (puncturedPair ℝ 0)).d 0
      ((ComplexShape.down ℕ).next 0)).hom
      (((relativeChainProjection ℚ (puncturedPair ℝ 0)).f 0).hom
        (chainOfSimplex ℚ (standardSingularSimplex 0))) = 0 := by
    rw [hc9kc_d_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
  rw [hstd, hc9kc_standardLocalClass_eq_chainClass 0 hc0, hc9kc_chainClass_map,
    ← hu, hc9kc_dualClass_chainClass, chainOfSimplex_map] at h1
  convert h1 using 3
  apply ((TopCat.of (Fin 0 → ℂ)).toSSetObjEquiv _).injective
  ext t i
  exact i.elim0


open scoped Simplicial in
private theorem hc9kc_cochain_ext {X : SSet.{0}} {n : ℕ} (φ ψ : Cochain ℚ X n)
    (h : ∀ σ : X _⦋n⦌, φ (chainOfSimplex ℚ σ) = ψ (chainOfSimplex ℚ σ)) : φ = ψ := by
  have hc : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := by
    apply SSet.chainComplex_hom_ext
    intro σ
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    have hi : (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom a =
        a • chainOfSimplex ℚ σ := by
      rw [chainOfSimplex, ← map_smul]
      simp
    change φ ((X.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom a) =
      ψ ((X.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom a)
    rw [hi, map_smul, map_smul, h]
  exact congrArg ModuleCat.Hom.hom hc

open scoped Simplicial in
private theorem hc9kc_relativeChain_simplex_zero (Y : TopCat.{0}) (B : Set Y) (k : ℕ)
    (σ : (TopCat.toSSet.obj Y) _⦋k⦌) (hσ : ∀ t, Y.toSSetObjEquiv _ σ t ∈ B) :
    ((relativeChainProjection ℚ (TopPair.ofSubset (X := Y) B)).f k).hom
      (chainOfSimplex ℚ σ) = 0 := by
  let τ := ((TopCat.of ↥B).toSSetObjEquiv _).symm
    ⟨fun t => ⟨Y.toSSetObjEquiv _ σ t, hσ t⟩, by fun_prop⟩
  have hτ : (TopCat.toSSet.map (TopPair.ofSubset (X := Y) B).map).app _ τ = σ := by
    apply (Y.toSSetObjEquiv _).injective
    rfl
  have hz := ConcreteCategory.congr_hom (congrArg (fun f ↦ f.f k)
    (subspaceChainMap_relativeChainProjection ℚ (TopPair.ofSubset (X := Y) B)))
    (chainOfSimplex ℚ τ)
  change ((relativeChainProjection ℚ _).f k).hom
    ((((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := Y) B)).hom.f k).hom
      (chainOfSimplex ℚ τ)) = 0 at hz
  rw [← hτ, ← chainOfSimplex_map]
  exact hz

/-- A chain whose boundary consists of simplices in `B` is a relative cycle modulo `B`. -/
private theorem hc9kc_relativeCycle_of_span (Y : TopCat.{0}) (B : Set Y) {ι : Type}
    (F : ι → Set Y) (hF : ∀ i, F i ⊆ B) (N : ℕ)
    (x : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X N)
    (hx : ∀ m, (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d N m).hom x ∈
      hc9kc_smallSpan Y F m) :
    (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := Y) B)).d N
        ((ComplexShape.down ℕ).next N)).hom
      (((relativeChainProjection ℚ (TopPair.ofSubset (X := Y) B)).f N).hom x) = 0 := by
  have hd := ConcreteCategory.congr_hom
    ((relativeChainProjection ℚ (TopPair.ofSubset (X := Y) B)).comm N
      ((ComplexShape.down ℕ).next N)) x
  change (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := Y) B)).d N _).hom
      (((relativeChainProjection ℚ (TopPair.ofSubset (X := Y) B)).f N).hom x) =
    ((relativeChainProjection ℚ (TopPair.ofSubset (X := Y) B)).f _).hom
      ((((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d N _).hom x) at hd
  rw [hd]
  refine hc9kc_smallSpan_le_ker Y F _
    ((relativeChainProjection ℚ (TopPair.ofSubset (X := Y) B)).f _).hom
    (fun σ i hσ => ?_) (hx _)
  exact hc9kc_relativeChain_simplex_zero Y B _ σ (fun t => hF i (hσ t))

private theorem hc9kc_pairing_transport_chainClass (Y : TopCat.{0}) {A B : Closeds Y}
    (h : A = B) {m n : ℕ} (k : m = n)
    (U : RelativeCohomology ℚ (TopPair.ofSubset (A : Set Y)ᶜ) m)
    (x : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X n)
    (hx : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := Y) (B : Set Y)ᶜ)).d n
        ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ (TopPair.ofSubset (X := Y) (B : Set Y)ᶜ)).f n).hom x) = 0)
    (hx' : (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := Y) (A : Set Y)ᶜ)).d m
        ((ComplexShape.down ℕ).next m)).hom
      (((relativeChainProjection ℚ (TopPair.ofSubset (X := Y) (A : Set Y)ᶜ)).f m).hom
        ((((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).XIsoOfEq k.symm).hom.hom x))
          = 0) :
    relativeCohomologyEquivDualHomology ℚ _ n (hc9kc_transport h k U)
        (hc9kc_chainClass _ n x hx) =
      relativeCohomologyEquivDualHomology ℚ _ m U (hc9kc_chainClass _ m
        ((((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).XIsoOfEq k.symm).hom.hom x)
          hx') := by
  subst h k
  congr 1

open scoped Simplicial in
/-- A relative class whose representative is one on every vertex is a left unit. -/
private theorem hc9kc_relativeCup_unit (Y : TopCat.{0}) (S T : Closeds Y)
    (hS : (T : Set Y) ⊆ S) (q : ℕ)
    (u : LinearMap.ker (ccm15_relativeDual Y S 0).g.hom)
    (hu : ∀ σ : (TopCat.toSSet.obj Y) _⦋0⦌,
      relativeCochainToAbsolute ℚ (TopPair.ofSubset (S : Set Y)ᶜ) 0 u.1
        (chainOfSimplex ℚ σ) = 1)
    (V : RelativeCohomology ℚ (TopPair.ofSubset (T : Set Y)ᶜ) q) :
    ccm15_relativeCup Y S T 0 q
      (hc9kc_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (S : Set Y)ᶜ)) 0 u) V =
      hc9kc_transport (A := T) (B := S ⊓ T) (by
          ext y
          simp only [Closeds.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
          exact ⟨fun h => ⟨hS h, h⟩, fun h => h.2⟩)
        (Nat.zero_add q).symm V := by
  obtain ⟨v, rfl⟩ := hc9kc_dualClass_surjective _ q V
  apply (relativeCohomologyEquivDualHomology ℚ _ (0 + q)).injective
  apply LinearMap.ext
  intro h
  let F : Fin 2 → Set Y := ![(S : Set Y)ᶜ, (T : Set Y)ᶜ]
  have hopen : ∀ i, IsOpen (F i) := by
    intro i
    fin_cases i
    · exact S.isClosed.isOpen_compl
    · exact T.isClosed.isOpen_compl
  have hcover : ⋃ i, F i = ((S ⊓ T : Closeds Y) : Set Y)ᶜ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_compl_iff, Closeds.coe_inf, Set.mem_inter_iff,
      not_and_or, Fin.exists_fin_succ, Fin.exists_fin_zero, F, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_one, Fin.succ_zero_eq_one]
    tauto
  obtain ⟨x, hx, rfl, hsmall⟩ := hc9kc_exists_small_representative Y _ F hopen hcover
    (0 + q) h
  have hsm := hc9kc_small_all Y F _ x hsmall
  have hF : ∀ i, ∃ bb, F i ⊆ ccm13_complementFamily Y (S : Set Y) (T : Set Y) bb := by
    intro i
    fin_cases i
    · exact ⟨false, fun y hy => hy⟩
    · exact ⟨true, fun y hy => hy⟩
  have hxc := hc9kc_small_cycle Y _ _ F hF _ x hsm
  have hFT : ∀ i, F i ⊆ (T : Set Y)ᶜ := by
    intro i
    fin_cases i
    · exact fun y hy hT => hy (hS hT)
    · exact fun y hy => hy
  let x' := (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).XIsoOfEq
    (Nat.zero_add q)).hom.hom x
  have hx' := hc9kc_relativeCycle_of_span Y _ F hFT q x'
    (hc9kc_small_cast Y F (Nat.zero_add q) x hsm)
  rw [hc9kc_pairing_transport_chainClass Y _ (Nat.zero_add q).symm _ x hx hx',
    hc9kc_dualClass_chainClass]
  refine (hc9kc_relativeCup_eval Y S T 0 q u v x hxc).trans ?_
  have hunit : relativeCochainToAbsolute ℚ (TopPair.ofSubset (S : Set Y)ᶜ) 0 u.1 =
      unitCochain (R := ℚ) Y := by
    apply hc9kc_cochain_ext
    intro σ
    exact (hu σ).trans (unitCochain_apply_simplex Y σ).symm
  unfold ccm13_relativeCupLift
  rw [hunit, one_cupCochain]
  rfl

/-! ## Coordinate products in every normal dimension -/

private theorem hc9kc_relativeCup_transport_left (Y : TopCat.{0}) {S S' : Closeds Y}
    (T : Closeds Y) (hS : S = S') {p p' : ℕ} (kp : p = p') (q : ℕ)
    (U : RelativeCohomology ℚ (TopPair.ofSubset (S : Set Y)ᶜ) p)
    (V : RelativeCohomology ℚ (TopPair.ofSubset (T : Set Y)ᶜ) q) :
    ccm15_relativeCup Y S' T p' q (hc9kc_transport hS kp U) V =
      hc9kc_transport (by rw [hS]) (by rw [kp]) (ccm15_relativeCup Y S T p q U V) := by
  subst hS kp
  rfl

private theorem hc9kc_relativeCup_transport_right (Y : TopCat.{0}) (S : Closeds Y)
    {T T' : Closeds Y} (hT : T = T') (p : ℕ) {q q' : ℕ} (kq : q = q')
    (U : RelativeCohomology ℚ (TopPair.ofSubset (S : Set Y)ᶜ) p)
    (V : RelativeCohomology ℚ (TopPair.ofSubset (T : Set Y)ᶜ) q) :
    ccm15_relativeCup Y S T' p q' U (hc9kc_transport hT kq V) =
      hc9kc_transport (by rw [hT]) (by rw [kq]) (ccm15_relativeCup Y S T p q U V) := by
  subst hT kq
  rfl

/-- The zero support of two normal-coordinate maps placed side by side. -/
theorem hc9kc_zeroSupport_append {Y : TopCat.{0}} {p q : ℕ} (f : C(Y, Fin p → ℂ))
    (g : C(Y, Fin q → ℂ)) :
    ccm17_zeroSupport Y (p + q) (hc9k_appendCoordinates f g) =
      ccm17_zeroSupport Y p f ⊓ ccm17_zeroSupport Y q g := by
  ext y
  change (Fin.append (f y) (g y) : Fin (p + q) → ℂ) = 0 ↔ f y = 0 ∧ g y = 0
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · have := congrFun h (Fin.castAdd q i)
      rwa [Fin.append_left] at this
    · have := congrFun h (Fin.natAdd p i)
      rwa [Fin.append_right] at this
  · rintro ⟨h1, h2⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact congrFun h1 j
    · rw [Fin.append_right]
      exact congrFun h2 j

open scoped Simplicial in
/-- The normal class of a map to `ℂ⁰` has a representative equal to one on every vertex. -/
private theorem hc9kc_normalClass_zero_rep (Y : TopCat.{0}) (f : C(Y, Fin 0 → ℂ)) :
    ∃ u : LinearMap.ker (ccm15_relativeDual Y (ccm17_zeroSupport Y 0 f) 0).g.hom,
      hc9kc_dualClass _ 0 u = ccm17_normalClass Y 0 f ∧
      ∀ σ : (TopCat.toSSet.obj Y) _⦋0⦌,
        relativeCochainToAbsolute ℚ (TopPair.ofSubset (ccm17_zeroSupport Y 0 f : Set Y)ᶜ) 0
          u.1 (chainOfSimplex ℚ σ) = 1 := by
  obtain ⟨u₀, hu₀⟩ := hc9kc_dualClass_surjective
    ((relativeChainFunctor ℚ).obj (puncturedPair ℂ 0)) 0 (normalizedPointCoclass 0)
  refine ⟨ShortComplex.moduleCatCycleMap (ShortComplex.linearDualMap
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) 0).map
      ((relativeChainFunctor ℚ).map (ccm17_normalPair Y 0 f)))) u₀, ?_, ?_⟩
  · rw [← hc9kc_dualClass_naturality, hu₀]
    rfl
  · intro σ
    have h := hc9kc_absolute_pullback (ccm17_normalPair Y 0 f) 0 u₀.1
    change relativeCochainToAbsolute ℚ _ 0
      (u₀.1.comp (((relativeChainFunctor ℚ).map (ccm17_normalPair Y 0 f)).f 0).hom)
        (chainOfSimplex ℚ σ) = 1
    rw [h, cochainMap_apply, chainOfSimplex_map]
    exact hc9kc_normalizedPointCoclass_zero_vertex u₀ hu₀ _

/-- The coordinate product with no head coordinates. -/
private theorem hc9kc_product_zero (Y : TopCat.{0}) (q : ℕ) (f : C(Y, Fin 0 → ℂ))
    (g : C(Y, Fin q → ℂ)) :
    ccm15_relativeCup Y (ccm17_zeroSupport Y 0 f) (ccm17_zeroSupport Y q g) (2 * 0) (2 * q)
        (ccm17_normalClass Y 0 f) (ccm17_normalClass Y q g) =
      hc9kc_transport (hc9kc_zeroSupport_append f g) (by ring)
        (ccm17_normalClass Y (0 + q) (hc9k_appendCoordinates f g)) := by
  obtain ⟨u, hu, hu1⟩ := hc9kc_normalClass_zero_rep Y f
  have hS : (ccm17_zeroSupport Y q g : Set Y) ⊆ ccm17_zeroSupport Y 0 f :=
    fun y _ => (show f y = 0 from funext fun i => i.elim0)
  have hU := hc9kc_relativeCup_unit Y _ _ hS (2 * q) u hu1 (ccm17_normalClass Y q g)
  rw [hu] at hU
  have happ : hc9kc_reindex (Nat.zero_add q) g = hc9k_appendCoordinates f g := by
    ext y i
    refine Fin.addCases (fun j => j.elim0) (fun j => ?_) i
    change g y (Fin.cast (Nat.zero_add q) (Fin.natAdd 0 j)) = Fin.append (f y) (g y) (Fin.natAdd 0 j)
    rw [Fin.append_right]
    exact congrArg (g y) (Fin.ext (by simp))
  rw [hc9kc_normalClass_congr Y (0 + q) happ, hc9kc_normalClass_reindex, hc9kc_transport_trans,
    hc9kc_transport_trans]
  exact hU

/-- The coordinate product of any two normal-coordinate maps.
Source: Bott--Tu, *Differential Forms in Algebraic Topology*, §6, Thom classes of direct sums. -/
theorem hc9kc_product_general (p : ℕ) : ∀ (Y : TopCat.{0}) (q : ℕ) (f : C(Y, Fin p → ℂ))
    (g : C(Y, Fin q → ℂ)),
    ccm15_relativeCup Y (ccm17_zeroSupport Y p f) (ccm17_zeroSupport Y q g) (2 * p) (2 * q)
        (ccm17_normalClass Y p f) (ccm17_normalClass Y q g) =
      hc9kc_transport (hc9kc_zeroSupport_append f g) (by ring)
        (ccm17_normalClass Y (p + q) (hc9k_appendCoordinates f g)) := by
  induction p with
  | zero => exact hc9kc_product_zero
  | succ p ih =>
    intro Y q f g
    let x : C(Y, Fin 1 → ℂ) := (ccm17_head p).comp f
    let r : C(Y, Fin p → ℂ) := (ccm17_tail p).comp f
    have hf : hc9kc_cons x r = f := by
      ext y i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rfl
    have hN := (hc9kc_transport_eq_iff _ _ _ _).mp (hc9kc_divisor_product Y p x r).symm
    have e : p + q + 1 = p + 1 + q := by omega
    have hcons : hc9kc_reindex e (hc9k_appendCoordinates f g) =
        hc9kc_cons x (hc9k_appendCoordinates r g) := by
      ext y i
      simp only [hc9kc_reindex, hc9kc_cons, hc9k_appendCoordinates, ContinuousMap.coe_mk]
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero, show (Fin.cast e 0 : Fin (p + 1 + q)) = Fin.castAdd q 0 from
          Fin.ext rfl, Fin.append_left]
        rfl
      · rw [Fin.cons_succ]
        refine Fin.addCases (fun k => ?_) (fun k => ?_) j
        · rw [show (Fin.cast e (Fin.castAdd q k).succ : Fin (p + 1 + q)) =
            Fin.castAdd q k.succ from Fin.ext rfl, Fin.append_left, Fin.append_left]
          rfl
        · rw [show (Fin.cast e (Fin.natAdd p k).succ : Fin (p + 1 + q)) =
            Fin.natAdd (p + 1) k from Fin.ext (by simp; omega), Fin.append_right,
            Fin.append_right]
    rw [hc9kc_normalClass_congr Y (p + 1) hf, hN, hc9kc_transport_trans,
      hc9kc_relativeCup_transport_left, hc9kc_relativeCup_assoc', hc9kc_transport_trans,
      ih Y q r g, hc9kc_relativeCup_transport_right, hc9kc_transport_trans,
      hc9kc_divisor_product Y (p + q) x (hc9k_appendCoordinates r g), hc9kc_transport_trans,
      hc9kc_normalClass_congr Y (p + q + 1) hcons, hc9kc_transport_trans,
      hc9kc_normalClass_reindex, hc9kc_transport_trans]

/-- The coordinate product in every normal dimension.
Source: Bott--Tu, *Differential Forms in Algebraic Topology*, §6, Thom classes of direct sums. -/
theorem hc9kc_coordinate_product (p q : ℕ) :
    ccm15_relativeCup (TopCat.of (Fin (p + q) → ℂ))
      (ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) p (hc9k_coordinateHead p q))
      (ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) q (hc9k_coordinateTail p q))
      (2 * p) (2 * q)
      (ccm17_normalClass (TopCat.of (Fin (p + q) → ℂ)) p (hc9k_coordinateHead p q))
      (ccm17_normalClass (TopCat.of (Fin (p + q) → ℂ)) q (hc9k_coordinateTail p q)) =
    hc9k_coordinateIntersectionClass p q := by
  have hid : (ContinuousMap.id (Fin (p + q) → ℂ) : C(TopCat.of (Fin (p + q) → ℂ), Fin (p + q) → ℂ)) =
      hc9k_appendCoordinates (hc9k_coordinateHead p q) (hc9k_coordinateTail p q) := by
    ext z i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact (Fin.append_left (fun k => z (Fin.castAdd q k)) (fun k => z (Fin.natAdd p k)) j).symm
    · exact (Fin.append_right (fun k => z (Fin.castAdd q k)) (fun k => z (Fin.natAdd p k)) j).symm
  have h1 := hc9kc_product_general p (TopCat.of (Fin (p + q) → ℂ)) q
    (hc9k_coordinateHead p q) (hc9k_coordinateTail p q)
  rw [h1, hc9kc_normalClass_congr _ (p + q) hid, hc9kc_transport_trans]
  have h2 : hc9k_coordinateIntersectionClass p q = hc9kc_transport rfl (by ring)
      (relativeCohomologyMap ℚ (2 * (p + q)) (hc9k_coordinateIntersectionPair p q)
        (normalizedPointCoclass (p + q))) :=
    hc9kc_eqRec_transport _ _ _
  rw [h2, ← hc9kc_transport_trans ((congrArg (ccm17_zeroSupport _ (p + q)) hid).trans
    (hc9kc_zeroSupport_append _ _)) rfl rfl (by ring)]
  congr 1
  exact hc9kc_transport_pullback (TopCat.of (Fin (p + q) → ℂ))
    (TopCat.of (Fin (p + q) → ℂ)) _ _ _ rfl _ _ _

/-- info: 'HodgeLean.Adapters.hc9kc_coordinate_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hc9kc_coordinate_product

/-- The normal class in dimension zero is a left unit for every relative support class.
Source: the relative Alexander--Whitney unit law, via the vertex normalization. -/
theorem a3cc2_relativeCup_normal_zero (Y : TopCat.{0}) (T : Closeds Y) (q : ℕ)
    (f : C(Y, Fin 0 → ℂ))
    (hT : T = ccm17_zeroSupport Y 0 f ⊓ T)
    (V : RelativeCohomology ℚ (TopPair.ofSubset (T : Set Y)ᶜ) q) :
    ccm15_relativeCup Y (ccm17_zeroSupport Y 0 f) T 0 q
      (ccm17_normalClass Y 0 f) V =
      hc9kc_transport hT (Nat.zero_add q).symm V := by
  obtain ⟨u, hu, hu1⟩ := hc9kc_normalClass_zero_rep Y f
  have hS : (T : Set Y) ⊆ ccm17_zeroSupport Y 0 f :=
    fun y _ => (show f y = 0 from Subsingleton.elim _ _)
  rw [← hu]
  exact hc9kc_relativeCup_unit Y _ T hS q u hu1 V

#print axioms a3cc2_relativeCup_normal_zero

open scoped Simplicial in
/-- Pulling back the zero-dimensional normal class gives a unit on a contained support.
Source: the relative Alexander--Whitney unit law and normalization on vertices. -/
theorem a3cc2_relativeCup_normalPair_zero (Y : TopCat.{0}) (S T : Closeds Y)
    (hS : (T : Set Y) ⊆ S) (hT : T = S ⊓ T) (q : ℕ)
    (f : TopPair.ofSubset (S : Set Y)ᶜ ⟶ puncturedPair ℂ 0)
    (V : RelativeCohomology ℚ (TopPair.ofSubset (T : Set Y)ᶜ) q) :
    ccm15_relativeCup Y S T 0 q
      (relativeCohomologyMap ℚ 0 f (normalizedPointCoclass 0)) V =
      hc9kc_transport hT (Nat.zero_add q).symm V := by
  obtain ⟨u₀, hu₀⟩ := hc9kc_dualClass_surjective
    ((relativeChainFunctor ℚ).obj (puncturedPair ℂ 0)) 0 (normalizedPointCoclass 0)
  let u := ShortComplex.moduleCatCycleMap (ShortComplex.linearDualMap
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) 0).map
      ((relativeChainFunctor ℚ).map f))) u₀
  have hu : hc9kc_dualClass _ 0 u =
      relativeCohomologyMap ℚ 0 f (normalizedPointCoclass 0) := by
    rw [← hc9kc_dualClass_naturality, hu₀]
    rfl
  have hu1 : ∀ σ : (TopCat.toSSet.obj Y) _⦋0⦌,
      relativeCochainToAbsolute ℚ (TopPair.ofSubset (S : Set Y)ᶜ) 0 u.1
        (chainOfSimplex ℚ σ) = 1 := by
    intro σ
    have hpull := hc9kc_absolute_pullback f 0 u₀.1
    change relativeCochainToAbsolute ℚ _ 0
      (u₀.1.comp (((relativeChainFunctor ℚ).map f).f 0).hom) (chainOfSimplex ℚ σ) = 1
    rw [hpull, cochainMap_apply, chainOfSimplex_map]
    exact hc9kc_normalizedPointCoclass_zero_vertex u₀ hu₀ _
  rw [← hu]
  exact hc9kc_relativeCup_unit Y S T hS q u hu1 V

#print axioms a3cc2_relativeCup_normalPair_zero

open scoped Simplicial in
private theorem a3cc2_relativeCup_unit_right (Y : TopCat.{0}) (S T : Closeds Y)
    (hT : (S : Set Y) ⊆ T) (p : ℕ)
    (v : LinearMap.ker (ccm15_relativeDual Y T 0).g.hom)
    (hv : ∀ σ : (TopCat.toSSet.obj Y) _⦋0⦌,
      relativeCochainToAbsolute ℚ (TopPair.ofSubset (T : Set Y)ᶜ) 0 v.1
        (chainOfSimplex ℚ σ) = 1)
    (U : RelativeCohomology ℚ (TopPair.ofSubset (S : Set Y)ᶜ) p) :
    ccm15_relativeCup Y S T p 0 U
      (hc9kc_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (T : Set Y)ᶜ)) 0 v) =
      hc9kc_transport (A := S) (B := S ⊓ T) (by
          ext y
          simp only [Closeds.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
          exact ⟨fun h => ⟨h, hT h⟩, fun h => h.1⟩) rfl U := by
  obtain ⟨u, rfl⟩ := hc9kc_dualClass_surjective _ p U
  apply (relativeCohomologyEquivDualHomology ℚ _ (p + 0)).injective
  apply LinearMap.ext
  intro h
  let F : Fin 2 → Set Y := ![(S : Set Y)ᶜ, (T : Set Y)ᶜ]
  have hopen : ∀ i, IsOpen (F i) := by
    intro i
    fin_cases i
    · exact S.isClosed.isOpen_compl
    · exact T.isClosed.isOpen_compl
  have hcover : ⋃ i, F i = ((S ⊓ T : Closeds Y) : Set Y)ᶜ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_compl_iff, Closeds.coe_inf, Set.mem_inter_iff,
      not_and_or, Fin.exists_fin_succ, Fin.exists_fin_zero, F, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    tauto
  obtain ⟨x, hx, rfl, hsmall⟩ := hc9kc_exists_small_representative Y _ F hopen hcover p h
  have hsm := hc9kc_small_all Y F _ x hsmall
  have hF : ∀ i, ∃ bb, F i ⊆ ccm13_complementFamily Y (S : Set Y) (T : Set Y) bb := by
    intro i
    fin_cases i
    · exact ⟨false, fun y hy => hy⟩
    · exact ⟨true, fun y hy => hy⟩
  have hxc := hc9kc_small_cycle Y _ _ F hF _ x hsm
  have hFS : ∀ i, F i ⊆ (S : Set Y)ᶜ := by
    intro i
    fin_cases i
    · exact fun y hy => hy
    · exact fun y hy hS => hy (hT hS)
  have hx' := hc9kc_relativeCycle_of_span Y _ F hFS p x hsm
  refine (hc9kc_relativeCup_eval Y S T p 0 u v x hxc).trans ?_
  refine Eq.trans ?_ ((hc9kc_dualClass_chainClass _ p u x hx').symm.trans
    (hc9kc_pairing_transport_chainClass Y _ rfl _ x hx hx').symm)
  have hunit : relativeCochainToAbsolute ℚ (TopPair.ofSubset (T : Set Y)ᶜ) 0 v.1 =
      unitCochain (R := ℚ) Y := by
    apply hc9kc_cochain_ext
    intro σ
    exact (hv σ).trans (unitCochain_apply_simplex Y σ).symm
  unfold ccm13_relativeCupLift
  rw [hunit, cupCochain_one]
  rfl

open scoped Simplicial in
/-- The zero-dimensional normal class acts as a right unit on a contained support.
Source: the relative Alexander--Whitney unit law and normalization on vertices. -/
theorem a3cc2_relativeCup_normalPair_zero_right (Y : TopCat.{0}) (S T : Closeds Y)
    (hT : (S : Set Y) ⊆ T) (hS : S = S ⊓ T) (p : ℕ)
    (f : TopPair.ofSubset (T : Set Y)ᶜ ⟶ puncturedPair ℂ 0)
    (U : RelativeCohomology ℚ (TopPair.ofSubset (S : Set Y)ᶜ) p) :
    ccm15_relativeCup Y S T p 0 U
      (relativeCohomologyMap ℚ 0 f (normalizedPointCoclass 0)) =
      hc9kc_transport hS rfl U := by
  obtain ⟨v₀, hv₀⟩ := hc9kc_dualClass_surjective
    ((relativeChainFunctor ℚ).obj (puncturedPair ℂ 0)) 0 (normalizedPointCoclass 0)
  let v := ShortComplex.moduleCatCycleMap (ShortComplex.linearDualMap
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) 0).map
      ((relativeChainFunctor ℚ).map f))) v₀
  have hv : hc9kc_dualClass _ 0 v =
      relativeCohomologyMap ℚ 0 f (normalizedPointCoclass 0) := by
    rw [← hc9kc_dualClass_naturality, hv₀]
    rfl
  have hv1 : ∀ σ : (TopCat.toSSet.obj Y) _⦋0⦌,
      relativeCochainToAbsolute ℚ (TopPair.ofSubset (T : Set Y)ᶜ) 0 v.1
        (chainOfSimplex ℚ σ) = 1 := by
    intro σ
    have hpull := hc9kc_absolute_pullback f 0 v₀.1
    change relativeCochainToAbsolute ℚ _ 0
      (v₀.1.comp (((relativeChainFunctor ℚ).map f).f 0).hom) (chainOfSimplex ℚ σ) = 1
    rw [hpull, cochainMap_apply, chainOfSimplex_map]
    exact hc9kc_normalizedPointCoclass_zero_vertex v₀ hv₀ _
  rw [← hv]
  exact a3cc2_relativeCup_unit_right Y S T hT p v hv1 U

#print axioms a3cc2_relativeCup_normalPair_zero_right

end HodgeLean.Adapters
