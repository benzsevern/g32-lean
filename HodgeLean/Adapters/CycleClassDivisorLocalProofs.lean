import HodgeLean.Adapters.CycleClassDivisorLocalDefs

/-! # Local orientation product obligations
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Adapters

open CategoryTheory.Limits AlgebraicTopology.Simplicial HodgeLean.Foundations.Singular

private theorem ccm17_absolute_pullback {P Q : TopPair.{0}} (f : P ⟶ Q)
    (n : ℕ) (u : RelativeCochain ℚ Q n) :
    relativeCochainToAbsolute ℚ P n
      (u.comp (((relativeChainFunctor ℚ).map f).f n).hom) =
    cochainMap ℚ (TopCat.toSSet.map (TopPair.Hom.fst f)) n
      (relativeCochainToAbsolute ℚ Q n u) := by
  ext c
  exact congrArg u (ConcreteCategory.congr_hom
    (congrArg (fun g => g.f n)
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)) c)

private theorem ccm17_relativeCupLift_pullback (Y Z : TopCat.{0}) (f : C(Y, Z))
    (S T : Closeds Z) (p q : ℕ)
    (u : RelativeCochain ℚ (TopPair.ofSubset (S : Set Z)ᶜ) p)
    (v : RelativeCochain ℚ (TopPair.ofSubset (T : Set Z)ᶜ) q) :
    cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom f)) (p + q)
      (ccm13_relativeCupLift Z S T p q u v) =
    ccm13_relativeCupLift Y (S.preimage f.continuous) (T.preimage f.continuous) p q
      (u.comp (((relativeChainFunctor ℚ).map (ccm17_preimagePair Y Z f S)).f p).hom)
      (v.comp (((relativeChainFunctor ℚ).map (ccm17_preimagePair Y Z f T)).f q).hom) := by
  unfold ccm13_relativeCupLift
  rw [ccm17_absolute_pullback, ccm17_absolute_pullback]
  exact cupCochain_naturality Z (TopCat.ofHom f) p q _ _

private def ccm17_smallMap (Y Z : TopCat.{0}) (f : C(Y, Z)) (S T : Closeds Z) :
    (coverSmallSingularSubcomplex Y
      (ccm13_complementFamily Y (S.preimage f.continuous) (T.preimage f.continuous)) : SSet) ⟶
    (coverSmallSingularSubcomplex Z (ccm13_complementFamily Z S T) : SSet) := by
  apply SSet.Subcomplex.lift
    ((coverSmallSingularSubcomplex Y
      (ccm13_complementFamily Y (S.preimage f.continuous) (T.preimage f.continuous))).ι ≫
      TopCat.toSSet.map (TopCat.ofHom f))
  intro n σ hσ
  obtain ⟨σ, rfl⟩ := hσ
  obtain ⟨b, τ, hτ⟩ := (mem_coverSmallSingularSubcomplex_iff_exists_preimage Y _ σ.1).mp σ.2
  let j : TopCat.of (ccm13_complementFamily Y
      (S.preimage f.continuous) (T.preimage f.continuous) b) ⟶
      TopCat.of (ccm13_complementFamily Z S T b) :=
    TopCat.ofHom ⟨fun x => ⟨f x.1, by cases b <;> exact x.2⟩, by fun_prop⟩
  apply (mem_coverSmallSingularSubcomplex_iff_exists_preimage Z _ _).mpr
  refine ⟨b, (TopCat.toSSet.map j).app n τ, ?_⟩
  change (TopCat.toSSet.map j ≫ TopCat.toSSet.map
      (topologicalSubsetInclusion Z (ccm13_complementFamily Z S T b))).app n τ =
    (TopCat.toSSet.map (TopCat.ofHom f)).app n σ.1
  rw [← Functor.map_comp]
  have hj : j ≫ topologicalSubsetInclusion Z (ccm13_complementFamily Z S T b) =
      topologicalSubsetInclusion Y (ccm13_complementFamily Y
        (S.preimage f.continuous) (T.preimage f.continuous) b) ≫ TopCat.ofHom f := rfl
  rw [hj, Functor.map_comp]
  exact congrArg ((TopCat.toSSet.map (TopCat.ofHom f)).app n) hτ

private theorem ccm17_smallMap_inclusion (Y Z : TopCat.{0}) (f : C(Y, Z))
    (S T : Closeds Z) :
    SSet.chainComplexMap (ccm17_smallMap Y Z f S T) (ModuleCat.of ℚ ℚ) ≫
      ccm14_smallInclusion Z S T =
    ccm14_smallInclusion Y (S.preimage f.continuous) (T.preimage f.continuous) ≫
      SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℚ ℚ) := by
  change SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _ =
    SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _
  simp only [SSet.chainComplexMap, ← Functor.map_comp]
  rfl

private def ccm17_smallRelativeMap (Y Z : TopCat.{0}) (f : C(Y, Z))
    (S T : Closeds Z) :
    ccm14_smallRelativeComplex Y (S.preimage f.continuous) (T.preimage f.continuous) ⟶
      ccm14_smallRelativeComplex Z S T :=
  CategoryTheory.Limits.cokernel.desc _
    (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℚ ℚ) ≫
      ccm14_smallProjection Z S T) (by
    rw [← Category.assoc, ← ccm17_smallMap_inclusion, Category.assoc]
    change _ ≫ (ccm14_smallInclusion Z S T ≫ CategoryTheory.Limits.cokernel.π _) = 0
    rw [CategoryTheory.Limits.cokernel.condition, comp_zero])

private theorem ccm17_smallRelativeMap_projection (Y Z : TopCat.{0}) (f : C(Y, Z))
    (S T : Closeds Z) :
    ccm14_smallProjection Y (S.preimage f.continuous) (T.preimage f.continuous) ≫
      ccm17_smallRelativeMap Y Z f S T =
    SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℚ ℚ) ≫
      ccm14_smallProjection Z S T := CategoryTheory.Limits.cokernel.π_desc _ _ _

private theorem ccm17_comparison_naturality (Y Z : TopCat.{0}) (f : C(Y, Z))
    (S T : Closeds Z) :
    ccm17_smallRelativeMap Y Z f S T ≫ ccm14_relativeComparison Z S T =
    ccm14_relativeComparison Y (S.preimage f.continuous) (T.preimage f.continuous) ≫
      (relativeChainFunctor ℚ).map (ccm17_preimagePair Y Z f (S ⊓ T)) := by
  letI : Epi (ccm14_smallProjection Y (S.preimage f.continuous)
      (T.preimage f.continuous)) := by
    unfold ccm14_smallProjection
    infer_instance
  apply (cancel_epi (ccm14_smallProjection Y (S.preimage f.continuous)
    (T.preimage f.continuous))).mp
  rw [← Category.assoc, ccm17_smallRelativeMap_projection, Category.assoc]
  change _ ≫ (cokernel.π _ ≫ cokernel.desc _ _ _) =
    cokernel.π _ ≫ cokernel.desc _ _ _ ≫ _
  rw [cokernel.π_desc, ← Category.assoc, cokernel.π_desc]
  exact (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
    (ccm17_preimagePair Y Z f (S ⊓ T))).symm

private theorem ccm17_smallCup_pullback (Y Z : TopCat.{0}) (f : C(Y, Z))
    (S T : Closeds Z) (p q : ℕ)
    (u : RelativeCochain ℚ (TopPair.ofSubset (S : Set Z)ᶜ) p)
    (v : RelativeCochain ℚ (TopPair.ofSubset (T : Set Z)ᶜ) q) :
    (ccm14_smallRelativeCup Z S T p q u v).comp
      ((ccm17_smallRelativeMap Y Z f S T).f (p + q)).hom =
    ccm14_smallRelativeCup Y (S.preimage f.continuous) (T.preimage f.continuous) p q
      (u.comp (((relativeChainFunctor ℚ).map (ccm17_preimagePair Y Z f S)).f p).hom)
      (v.comp (((relativeChainFunctor ℚ).map (ccm17_preimagePair Y Z f T)).f q).hom) := by
  apply ModuleCat.hom_ext_iff.mp
  apply Cofork.IsColimit.hom_ext (ccm14_projectionIsCokernel Y
    (S.preimage f.continuous) (T.preimage f.continuous) (p + q))
  apply ModuleCat.hom_ext
  change ((ccm14_smallRelativeCup Z S T p q u v).comp
    ((ccm17_smallRelativeMap Y Z f S T).f (p + q)).hom).comp
      ((ccm14_smallProjection Y (S.preimage f.continuous)
        (T.preimage f.continuous)).f (p + q)).hom =
    (ccm14_smallRelativeCup Y (S.preimage f.continuous) (T.preimage f.continuous) p q
      (u.comp (((relativeChainFunctor ℚ).map (ccm17_preimagePair Y Z f S)).f p).hom)
      (v.comp (((relativeChainFunctor ℚ).map (ccm17_preimagePair Y Z f T)).f q).hom)).comp
      ((ccm14_smallProjection Y (S.preimage f.continuous)
        (T.preimage f.continuous)).f (p + q)).hom
  rw [ccm15_smallCup_projection]
  ext c
  have h := ConcreteCategory.congr_hom (congrArg (fun g => g.f (p + q))
    (ccm17_smallRelativeMap_projection Y Z f S T)) c
  change ((ccm17_smallRelativeMap Y Z f S T).f (p + q)).hom
    (((ccm14_smallProjection Y (S.preimage f.continuous)
      (T.preimage f.continuous)).f (p + q)).hom c) =
    ((ccm14_smallProjection Z S T).f (p + q)).hom
      ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
        (ModuleCat.of ℚ ℚ)).f (p + q) c) at h
  simp only [LinearMap.comp_apply]
  rw [h]
  exact (LinearMap.congr_fun (ccm15_smallCup_projection Z S T p q u v) _).trans
    (LinearMap.congr_fun (ccm17_relativeCupLift_pullback Y Z f S T p q u v) c)

private def ccm17_dualEquiv (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :=
  (ShortComplex.homologyMapIso
    (HomologicalComplex.linearDualCochainComplexScIso K n)).toLinearEquiv.symm

private def ccm17_dualClass (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :=
  (ccm17_dualEquiv K n).toLinearMap.comp (K.sc n).linearDual.moduleCatHomologyClass

private theorem ccm17_dualClass_naturality
    {K L : ChainComplex (ModuleCat ℚ) ℕ} (f : K ⟶ L) (n : ℕ)
    (u : LinearMap.ker (L.sc n).linearDual.g.hom) :
    HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap f) n
        (ccm17_dualClass L n u) =
      ccm17_dualClass K n (ShortComplex.moduleCatCycleMap
        (ShortComplex.linearDualMap
          ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) n).map f)) u) := by
  apply (ccm17_dualEquiv K n).symm.injective
  have h := congrArg (ShortComplex.homologyFunctor (ModuleCat ℚ)).map
    (HomologicalComplex.linearDualCochainComplexScIso_naturality f n)
  rw [Functor.map_comp, Functor.map_comp] at h
  have hh := ConcreteCategory.congr_hom h (ccm17_dualClass L n u)
  change (ccm17_dualEquiv K n).symm
      (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap f) n
        (ccm17_dualClass L n u)) =
    (ShortComplex.homologyMap (ShortComplex.linearDualMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) n).map f))).hom
      ((ccm17_dualEquiv L n).symm
      (ccm17_dualClass L n u)) at hh
  rw [hh]
  simp only [ccm17_dualClass, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]
  exact ShortComplex.moduleCatHomologyClass_naturality _ u

private theorem ccm17_relativeCup_class (Y : TopCat.{0}) (S T : Closeds Y) (p q : ℕ)
    (u : LinearMap.ker (ccm15_relativeDual Y S p).g.hom)
    (v : LinearMap.ker (ccm15_relativeDual Y T q).g.hom) :
    ccm15_relativeCup Y S T p q
      (ccm17_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (S : Set Y)ᶜ)) p u)
      (ccm17_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (T : Set Y)ᶜ)) q v) =
    ccm15_dualTransport Y S T S.isClosed T.isClosed (p + q)
      ((ccm15_smallDual Y S T (p + q)).moduleCatHomologyClass
        (ccm15_cycleCup Y S T p q u v)) := by
  change ccm15_dualTransport Y S T S.isClosed T.isClosed (p + q)
    ((ccm15_smallDual Y S T (p + q)).moduleCatHomologyIso.inv.hom
      (ccm15_quotientCup Y S T p q
        ((ccm15_relativeDual Y S p).moduleCatHomologyIso.hom.hom
          ((ccm17_dualEquiv _ p).symm (ccm17_dualClass _ p u)))
        ((ccm15_relativeDual Y T q).moduleCatHomologyIso.hom.hom
          ((ccm17_dualEquiv _ q).symm (ccm17_dualClass _ q v))))) = _
  simp only [ccm17_dualClass, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
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

private theorem ccm17_comparison_transport (Y : TopCat.{0}) (S T : Closeds Y)
    (n : ℕ) (w : (ccm15_smallDual Y S T n).homology) :
    HomologicalComplex.homologyMap
      (HomologicalComplex.linearDualMap (ccm14_relativeComparison Y S T)) n
      (ccm15_dualTransport Y S T S.isClosed T.isClosed n w) =
    ccm17_dualEquiv (ccm14_smallRelativeComplex Y S T) n w := by
  letI := ccm15_dualComparison_quasiIso_aux Y S T S.isClosed T.isClosed
  exact (asIso (HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap (ccm14_relativeComparison Y S T)) n)).toLinearEquiv.apply_symm_apply _

attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData

private theorem ccm17_dualClass_evaluation
    (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (u : LinearMap.ker (K.sc n).f.hom.dualMap)
    (z : LinearMap.ker (K.sc n).g.hom) :
    K.linearDualHomologyEquiv n (ccm17_dualClass K n u)
      ((K.sc n).moduleCatHomologyClass z) = (u.1 : Module.Dual ℚ (K.X n)) z.1 := by
  change (K.sc n).linearDualHomologyEquiv
    ((ccm17_dualEquiv K n).symm (ccm17_dualClass K n u)) _ = _
  simp only [ccm17_dualClass, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]
  exact ShortComplex.linearDualHomologyEquiv_class_apply_class (K.sc n) u z

private theorem ccm17_relativeCup_evaluation (Y : TopCat.{0})
    (S T : Closeds Y) (p q : ℕ)
    (u : LinearMap.ker (ccm15_relativeDual Y S p).g.hom)
    (v : LinearMap.ker (ccm15_relativeDual Y T q).g.hom)
    (z : LinearMap.ker ((ccm14_smallRelativeComplex Y S T).sc (p + q)).g.hom) :
    relativeCohomologyEquivDualHomology ℚ
      (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ) (p + q)
      (ccm15_relativeCup Y S T p q
        (ccm17_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (S : Set Y)ᶜ)) p u)
        (ccm17_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (T : Set Y)ᶜ)) q v))
      (HomologicalComplex.homologyMap (ccm14_relativeComparison Y S T) (p + q)
        (((ccm14_smallRelativeComplex Y S T).sc (p + q)).moduleCatHomologyClass z)) =
      ccm14_smallRelativeCup Y S T p q u.1 v.1 z.1 := by
  rw [ccm17_relativeCup_class]
  change ((relativeChainFunctor ℚ).obj _).linearDualHomologyEquiv (p + q) _ _ = _
  refine (HomologicalComplex.linearDualHomologyEquiv_naturality
    (ccm14_relativeComparison Y S T) (p + q) _ _).symm.trans ?_
  rw [ccm17_comparison_transport]
  exact ccm17_dualClass_evaluation _ _ (ccm15_cycleCup Y S T p q u v) z

private theorem ccm17_relativeCup_evaluation_lift (Y : TopCat.{0})
    (S T : Closeds Y) (p q : ℕ)
    (u : LinearMap.ker (ccm15_relativeDual Y S p).g.hom)
    (v : LinearMap.ker (ccm15_relativeDual Y T q).g.hom)
    (z : LinearMap.ker ((ccm14_smallRelativeComplex Y S T).sc (p + q)).g.hom)
    (c : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X (p + q))
    (hc : ((ccm14_smallProjection Y S T).f (p + q)).hom c = z.1) :
    relativeCohomologyEquivDualHomology ℚ
      (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ) (p + q)
      (ccm15_relativeCup Y S T p q
        (ccm17_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (S : Set Y)ᶜ)) p u)
        (ccm17_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (T : Set Y)ᶜ)) q v))
      (HomologicalComplex.homologyMap (ccm14_relativeComparison Y S T) (p + q)
        (((ccm14_smallRelativeComplex Y S T).sc (p + q)).moduleCatHomologyClass z)) =
      ccm13_relativeCupLift Y S T p q u.1 v.1 c := by
  rw [ccm17_relativeCup_evaluation, ← hc]
  exact LinearMap.congr_fun (ccm15_smallCup_projection Y S T p q u.1 v.1) c

open scoped Simplicial in
private theorem ccm17_relativeCupLift_sum (Y : TopCat.{0})
    (S T : Set Y) (p q : ℕ)
    (u : RelativeCochain ℚ (TopPair.ofSubset Sᶜ) p)
    (v : RelativeCochain ℚ (TopPair.ofSubset Tᶜ) q)
    {ι : Type} (s : Finset ι) (a : ι → ℚ)
    (σ : ι → (TopCat.toSSet.obj Y) _⦋p + q⦌) :
    ccm13_relativeCupLift Y S T p q u v
      (∑ i ∈ s, a i • chainOfSimplex ℚ (σ i)) =
    ∑ i ∈ s, a i *
      (relativeCochainToAbsolute ℚ (TopPair.ofSubset Sᶜ) p u
        (chainOfSimplex ℚ (frontFace (TopCat.toSSet.obj Y) (p := p) (q := q) (σ i))) *
      relativeCochainToAbsolute ℚ (TopPair.ofSubset Tᶜ) q v
        (chainOfSimplex ℚ (backFace (TopCat.toSSet.obj Y) (p := p) (q := q) (σ i)))) := by
  simp only [map_sum, map_smul, ccm13_relativeCupLift,
    cupCochain_apply_simplex, smul_eq_mul]
  rfl

private theorem ccm17_smallCycle_representative (Y : TopCat.{0})
    (S T : Closeds Y) (n : ℕ)
    (h : RelativeHomology ℚ (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ) n) :
    ∃ z : LinearMap.ker ((ccm14_smallRelativeComplex Y S T).sc n).g.hom,
      HomologicalComplex.homologyMap (ccm14_relativeComparison Y S T) n
        (((ccm14_smallRelativeComplex Y S T).sc n).moduleCatHomologyClass z) = h := by
  letI := ccm14_relativeComparison_quasiIso Y S T S.isClosed T.isClosed
  obtain ⟨w, hw⟩ := (asIso (HomologicalComplex.homologyMap
    (ccm14_relativeComparison Y S T) n)).toLinearEquiv.surjective h
  obtain ⟨z, rfl⟩ := ((ccm14_smallRelativeComplex Y S T).sc n).moduleCatHomologyClass_surjective w
  exact ⟨z, hw⟩

private theorem ccm17_smallCycle_lift (Y : TopCat.{0})
    (S T : Closeds Y) (n : ℕ)
    (z : LinearMap.ker ((ccm14_smallRelativeComplex Y S T).sc n).g.hom) :
    ∃ c : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X n,
      ((ccm14_smallProjection Y S T).f n).hom c = z.1 := by
  letI : Epi (ccm14_smallProjection Y S T) := by
    unfold ccm14_smallProjection
    infer_instance
  exact (ModuleCat.epi_iff_surjective ((ccm14_smallProjection Y S T).f n)).mp
    inferInstance z.1

private theorem ccm17_transport_cycle_naturality (Y Z : TopCat.{0}) (f : C(Y, Z))
    (S T : Closeds Z) (n : ℕ)
    (w : LinearMap.ker (ccm15_smallDual Z S T n).g.hom) :
    relativeCohomologyMap ℚ n (ccm17_preimagePair Y Z f (S ⊓ T))
      (ccm15_dualTransport Z S T S.isClosed T.isClosed n
        ((ccm15_smallDual Z S T n).moduleCatHomologyClass w)) =
    ccm15_dualTransport Y (S.preimage f.continuous) (T.preimage f.continuous)
      (S.preimage f.continuous).isClosed (T.preimage f.continuous).isClosed n
      ((ccm15_smallDual Y (S.preimage f.continuous) (T.preimage f.continuous) n).moduleCatHomologyClass
        (ShortComplex.moduleCatCycleMap (ShortComplex.linearDualMap
          ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) n).map
            (ccm17_smallRelativeMap Y Z f S T))) w)) := by
  letI := ccm15_dualComparison_quasiIso_aux Y
    (S.preimage f.continuous) (T.preimage f.continuous)
    (S.preimage f.continuous).isClosed (T.preimage f.continuous).isClosed
  apply (asIso (HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap (ccm14_relativeComparison Y
      (S.preimage f.continuous) (T.preimage f.continuous))) n)).toLinearEquiv.injective
  have h := congrArg (fun g => HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap g) n) (ccm17_comparison_naturality Y Z f S T)
  simp only [HomologicalComplex.linearDualMap_comp, HomologicalComplex.homologyMap_comp] at h
  have hh := ConcreteCategory.congr_hom h
    (ccm15_dualTransport Z S T S.isClosed T.isClosed n
      ((ccm15_smallDual Z S T n).moduleCatHomologyClass w))
  change HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap (ccm17_smallRelativeMap Y Z f S T)) n
    (HomologicalComplex.homologyMap
      (HomologicalComplex.linearDualMap (ccm14_relativeComparison Z S T)) n
      (ccm15_dualTransport Z S T S.isClosed T.isClosed n
        ((ccm15_smallDual Z S T n).moduleCatHomologyClass w))) = _ at hh
  change HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap (ccm14_relativeComparison Y
      (S.preimage f.continuous) (T.preimage f.continuous))) n _ = _
  refine hh.symm.trans ?_
  change HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap (ccm17_smallRelativeMap Y Z f S T)) n
      (HomologicalComplex.homologyMap
        (HomologicalComplex.linearDualMap (ccm14_relativeComparison Z S T)) n _) =
    HomologicalComplex.homologyMap
      (HomologicalComplex.linearDualMap (ccm14_relativeComparison Y
        (S.preimage f.continuous) (T.preimage f.continuous))) n _
  rw [ccm17_comparison_transport, ccm17_comparison_transport]
  exact ccm17_dualClass_naturality (ccm17_smallRelativeMap Y Z f S T) n w

private theorem ccm17_head_tail_zero (q : ℕ) (z : Fin (q + 1) → ℂ) :
    ccm17_head q z = 0 ∧ ccm17_tail q z = 0 ↔ z = 0 := by
  constructor
  · rintro ⟨hh, ht⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrFun hh 0
    · exact congrFun ht j
  · rintro rfl
    exact ⟨rfl, rfl⟩

private def ccm17_intersectionPairIso (q : ℕ) :
    TopPair.ofSubset (X := TopCat.of (Fin (q + 1) → ℂ))
      ((ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q) ⊓
        ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q) :
          Closeds (Fin (q + 1) → ℂ)) : Set (Fin (q + 1) → ℂ))ᶜ ≅
      puncturedPair ℂ (q + 1) :=
  TopPair.isoOfSubset (Homeomorph.refl _) (fun z => not_congr (ccm17_head_tail_zero q z).symm)

private theorem ccm17_intersectionPairIso_hom (q : ℕ) :
    (ccm17_intersectionPairIso q).hom = ccm17_intersectionPair q := by
  rfl

private theorem ccm17_pointCoclass_ext (c : ℕ)
    (u v : RelativeCohomology ℚ (puncturedPair ℂ c) (2 * c))
    (h : relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ c) (2 * c) u
        (standardComplexLocalClass ℚ c) =
      relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ c) (2 * c) v
        (standardComplexLocalClass ℚ c)) : u = v := by
  apply (relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ c) (2 * c)).injective
  apply LinearMap.ext_on (s := {standardComplexLocalClass ℚ c})
    (span_standardComplexLocalClass_eq_top_for_chart c)
  rintro _ rfl
  exact h

/-- Pairing with the fixed real generator is evaluation on its actual affine
simplex, before the relative chain projection. -/
private theorem ccm17_standardLocalClass_evaluation (d : ℕ)
    (u : (RelativeCochainComplex ℚ (puncturedPair ℝ d)).cycles d) :
    relativeCohomologyEquivDualHomology ℚ (puncturedPair ℝ d) d
      ((RelativeCochainComplex ℚ (puncturedPair ℝ d)).homologyπ d u)
      (standardLocalClass ℚ d) =
    relativeCochainToAbsolute ℚ (puncturedPair ℝ d) d
      ((RelativeCochainComplex ℚ (puncturedPair ℝ d)).iCycles d u)
      (chainOfSimplex ℚ (standardSingularSimplex d)) := by
  change (standardLocalRelativeChainComplex ℚ d).linearDualHomologyEquiv d
    ((RelativeCochainComplex ℚ (puncturedPair ℝ d)).homologyπ d u)
    ((standardLocalRelativeChainComplex ℚ d).homologyπ d
      ((standardLocalCycle ℚ d) 1)) = _
  rw [linearDualHomologyEquiv_homologyπ_homologyπ]
  change (show Module.Dual ℚ ((standardLocalRelativeChainComplex ℚ d).X d) from
    (RelativeCochainComplex ℚ (puncturedPair ℝ d)).iCycles d u)
    ((standardLocalCycle ℚ d ≫
    (standardLocalRelativeChainComplex ℚ d).iCycles d) 1) = _
  rw [standardLocalCycle_inclusion]
  rfl

#print axioms ccm17_standardLocalClass_evaluation

/-- The complex orientation pairing is evaluation after pulling the cocycle
back to the fixed real affine simplex in consecutive real and imaginary coordinates. -/
private theorem ccm17_standardComplexLocalClassMul_evaluation (c : ℕ)
    (u : (RelativeCochainComplex ℚ (puncturedPair ℂ c)).cycles (c * 2)) :
    relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ c) (c * 2)
      ((RelativeCochainComplex ℚ (puncturedPair ℂ c)).homologyπ (c * 2) u)
      (standardComplexLocalClassMul c) =
    relativeCochainToAbsolute ℚ (puncturedPair ℝ (c * 2)) (c * 2)
      ((relativeCochainComplexMap ℚ (standardComplexRealPairIso c).inv).f (c * 2)
        ((RelativeCochainComplex ℚ (puncturedPair ℂ c)).iCycles (c * 2) u))
      (chainOfSimplex ℚ (standardSingularSimplex (c * 2))) := by
  let f := relativeCochainComplexMap ℚ (standardComplexRealPairIso c).inv
  have hπ := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality f (c * 2)) u
  have hi := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i f (c * 2)) u
  simp only [ConcreteCategory.comp_apply] at hπ hi
  change relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ c) (c * 2)
    ((RelativeCochainComplex ℚ (puncturedPair ℂ c)).homologyπ (c * 2) u)
    (relativeHomologyMap ℚ (c * 2) (standardComplexRealPairIso c).inv
      (standardLocalClass ℚ (c * 2))) = _
  rw [← relativeCohomologyEquivDualHomology_relativeCohomologyMap]
  change relativeCohomologyEquivDualHomology ℚ (puncturedPair ℝ (c * 2)) (c * 2)
    (HomologicalComplex.homologyMap f (c * 2)
      ((RelativeCochainComplex ℚ (puncturedPair ℂ c)).homologyπ (c * 2) u)) _ = _
  rw [hπ, ccm17_standardLocalClass_evaluation, hi]

#print axioms ccm17_standardComplexLocalClassMul_evaluation

private theorem ccm17_normalizedPointCoclass_evaluation (c : ℕ) :
    relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ c) (2 * c)
      (normalizedPointCoclass c) (standardComplexLocalClass ℚ c) = 1 := by
  change (relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ c) (2 * c))
    ((relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ c) (2 * c)).symm
      (normalizedDual (standardComplexLocalClass ℚ c) _)) _ = _
  rw [LinearEquiv.apply_symm_apply]
  exact Classical.choose_spec (Module.Projective.exists_dual_eq_one ℚ
    (standardComplexLocalClass_ne_zero_for_chart c))

private theorem ccm17_pairing_degree_cast {P : TopPair.{0}} {m n : ℕ}
    (h : m = n) (u : RelativeCohomology ℚ P n) (z : RelativeHomology ℚ P m) :
    relativeCohomologyEquivDualHomology ℚ P m (h.symm ▸ u) z =
      relativeCohomologyEquivDualHomology ℚ P n u (h ▸ z) := by
  subst n
  rfl

#print axioms ccm17_pairing_degree_cast

/-- Choose a representative of the fixed normalized complex coclass, retaining
its value on the fixed affine simplex after transport to real coordinates. -/
private theorem ccm17_normalizedPointCoclass_representative (c : ℕ) :
    ∃ u : (RelativeCochainComplex ℚ (puncturedPair ℂ c)).cycles (c * 2),
      (RelativeCochainComplex ℚ (puncturedPair ℂ c)).homologyπ (c * 2) u =
        (Nat.mul_comm c 2).symm ▸ normalizedPointCoclass c ∧
      relativeCochainToAbsolute ℚ (puncturedPair ℝ (c * 2)) (c * 2)
        ((relativeCochainComplexMap ℚ (standardComplexRealPairIso c).inv).f (c * 2)
          ((RelativeCochainComplex ℚ (puncturedPair ℂ c)).iCycles (c * 2) u))
        (chainOfSimplex ℚ (standardSingularSimplex (c * 2))) = 1 := by
  obtain ⟨u, hu⟩ := (ModuleCat.epi_iff_surjective
    ((RelativeCochainComplex ℚ (puncturedPair ℂ c)).homologyπ (c * 2))).mp
    inferInstance ((Nat.mul_comm c 2).symm ▸ normalizedPointCoclass c)
  refine ⟨u, hu, ?_⟩
  rw [← ccm17_standardComplexLocalClassMul_evaluation, hu, ccm17_pairing_degree_cast]
  exact ccm17_normalizedPointCoclass_evaluation c

#print axioms ccm17_normalizedPointCoclass_representative

/-- Evaluation of the normalized coclass recovers the coefficient of the fixed
complex local homology generator. -/
private theorem ccm17_pointHomology_eq_evaluation_smul (c : ℕ)
    (z : RelativeHomology ℚ (puncturedPair ℂ c) (2 * c)) :
    z = (relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ c) (2 * c)
      (normalizedPointCoclass c) z) • standardComplexLocalClass ℚ c := by
  have hz : z ∈ Submodule.span ℚ {standardComplexLocalClass ℚ c} := by
    rw [span_standardComplexLocalClass_eq_top_for_chart]
    exact Submodule.mem_top
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
  rw [map_smul, ccm17_normalizedPointCoclass_evaluation, smul_eq_mul, mul_one]

#print axioms ccm17_pointHomology_eq_evaluation_smul

private theorem ccm17_eq_normalized_pullback {P : TopPair.{0}} (c : ℕ)
    (e : P ≅ puncturedPair ℂ c) (u : RelativeCohomology ℚ P (2 * c))
    (h : relativeCohomologyEquivDualHomology ℚ P (2 * c) u
      (relativeHomologyMap ℚ (2 * c) e.inv (standardComplexLocalClass ℚ c)) = 1) :
    u = relativeCohomologyMap ℚ (2 * c) e.hom (normalizedPointCoclass c) := by
  have hu : relativeCohomologyMap ℚ (2 * c) e.inv u = normalizedPointCoclass c := by
    apply ccm17_pointCoclass_ext
    rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
      ccm17_normalizedPointCoclass_evaluation]
    exact h
  have hh := congrArg (relativeCohomologyMap ℚ (2 * c) e.hom) hu
  change ((relativeCohomologyMap ℚ (2 * c) e.hom).comp
    (relativeCohomologyMap ℚ (2 * c) e.inv)) u = _ at hh
  rw [← relativeCohomologyMap_comp, e.hom_inv_id, relativeCohomologyMap_id] at hh
  exact hh

private theorem ccm17_normalClass_comp (Y Z : TopCat.{0}) (c : ℕ)
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

open Convexity in
/-- An affine simplex with an omitted vertex misses the origin, even when the
vertex map repeats vertices. -/
private theorem ccm17_affine_reparam_ne_zero {m d : ℕ}
    (f : Fin (m + 1) → Fin (d + 1)) (j : Fin (d + 1))
    (hj : ∀ i, f i ≠ j) (t : StdSimplex ℝ (Fin (m + 1))) :
    standardAffineSimplex d (StdSimplex.map f t) ≠ 0 := by
  apply standardAffineSimplex_ne_zero_of_coord_zero d _ j
  rw [StdSimplex.weights_map_apply]
  exact Finset.sum_eq_zero fun i hi => False.elim (hj i (Finset.mem_filter.mp hi).2)

#print axioms ccm17_affine_reparam_ne_zero

open scoped Simplicial in
open Convexity in
/-- The affine singular simplex obtained from an arbitrary map of vertices. -/
private def ccm17_affineReparam {m d : ℕ} (f : Fin (m + 1) → Fin (d + 1)) :
    (TopCat.toSSet.obj (TopCat.of (Fin d → ℝ))) _⦋m⦌ :=
  ((TopCat.of (Fin d → ℝ)).toSSetObjEquiv _).symm
    ⟨fun t => standardAffineSimplex d (StdSimplex.map f t), by fun_prop⟩

/-- Relative cochains vanish on affine simplices with an omitted vertex.
This uses support, so no normalization condition on degenerate cochains is needed. -/
private theorem ccm17_affineReparam_evaluation_zero {m d : ℕ}
    (f : Fin (m + 1) → Fin (d + 1)) (j : Fin (d + 1)) (hj : ∀ i, f i ≠ j)
    (u : RelativeCochain ℚ (puncturedPair ℝ d) m) :
    relativeCochainToAbsolute ℚ (puncturedPair ℝ d) m u
      (chainOfSimplex ℚ (ccm17_affineReparam f)) = 0 := by
  let τ := ((puncturedPair ℝ d).snd.toSSetObjEquiv (.op (SimplexCategory.mk m))).symm
    ⟨fun t => ⟨standardAffineSimplex d (Convexity.StdSimplex.map f t),
      ccm17_affine_reparam_ne_zero f j hj t⟩, by fun_prop⟩
  have hτ : (TopCat.toSSet.map (puncturedPair ℝ d).map).app _ τ =
      ccm17_affineReparam f := by
    apply ((puncturedPair ℝ d).fst.toSSetObjEquiv _).injective
    rfl
  have h := LinearMap.congr_fun
    (cochainMap_relativeCochainToAbsolute_eq_zero ℚ (puncturedPair ℝ d) m u)
    (chainOfSimplex ℚ τ)
  simpa only [cochainMap_apply, chainOfSimplex_map, hτ, LinearMap.zero_apply] using h

#print axioms ccm17_affineReparam_evaluation_zero

/-- A `(2,n)` shuffle is specified by the positions of its two left steps. -/
private abbrev ccm17_Shuffle (n : ℕ) :=
  {ab : Fin (n + 2) × Fin (n + 2) // ab.1 < ab.2}

private def ccm17_shuffleLeft {n : ℕ} (s : ccm17_Shuffle n)
    (i : Fin (2 + n + 1)) : Fin 3 :=
  ⟨(if s.1.1.val < i.val then 1 else 0) + (if s.1.2.val < i.val then 1 else 0), by
    split_ifs <;> omega⟩

private def ccm17_shuffleRight {n : ℕ} (s : ccm17_Shuffle n)
    (i : Fin (2 + n + 1)) : Fin (n + 1) :=
  ⟨i.val - (ccm17_shuffleLeft s i).val, by
    have ha := s.1.1.isLt
    have hb := s.1.2.isLt
    have hab : s.1.1.val < s.1.2.val := s.2
    have hi := i.isLt
    simp only [ccm17_shuffleLeft]
    split_ifs <;> omega⟩

private def ccm17_identityShuffle (n : ℕ) : ccm17_Shuffle n :=
  ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by change (0 : ℕ) < 1; omega⟩

/-- Any shuffle other than the ordered one omits the last left vertex on its
front two-face. -/
private theorem ccm17_shuffleLeft_front_omit {n : ℕ} (s : ccm17_Shuffle n)
    (hs : s ≠ ccm17_identityShuffle n) (i : Fin 3) :
    ccm17_shuffleLeft s ⟨i.val, by omega⟩ ≠ Fin.last 2 := by
  have hab : s.1.1.val < s.1.2.val := s.2
  have hb : 1 < s.1.2.val := by
    by_contra h
    have ha0 : s.1.1 = ⟨0, by omega⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
    have hb1 : s.1.2 = ⟨1, by omega⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
    apply hs
    apply Subtype.ext
    exact Prod.ext ha0 hb1
  intro he
  have hv := congrArg Fin.val he
  simp only [ccm17_shuffleLeft, Fin.val_last] at hv
  split_ifs at hv <;> omega

#print axioms ccm17_shuffleLeft_front_omit

open scoped Simplicial in
open Convexity in
/-- The affine product simplex for the lattice path of a shuffle. -/
private def ccm17_shuffleSimplex {n : ℕ} (s : ccm17_Shuffle n) :
    (TopCat.toSSet.obj (TopCat.of ((Fin 2 → ℝ) × (Fin n → ℝ)))) _⦋2 + n⦌ :=
  ((TopCat.of ((Fin 2 → ℝ) × (Fin n → ℝ))).toSSetObjEquiv _).symm
    ⟨fun t => (standardAffineSimplex 2 (StdSimplex.map (ccm17_shuffleLeft s) t),
      standardAffineSimplex n (StdSimplex.map (ccm17_shuffleRight s) t)), by fun_prop⟩

private theorem ccm17_shuffle_front_projection {n : ℕ} (s : ccm17_Shuffle n) :
    (TopCat.toSSet.map (TopCat.ofHom
      (⟨Prod.fst, continuous_fst⟩ : C((Fin 2 → ℝ) × (Fin n → ℝ), Fin 2 → ℝ)))).app _
      (frontFace _ (p := 2) (q := n) (ccm17_shuffleSimplex s)) =
    ccm17_affineReparam (fun i : Fin 3 => ccm17_shuffleLeft s ⟨i.val, by omega⟩) := by
  apply ((TopCat.of (Fin 2 → ℝ)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  change standardAffineSimplex 2
    (Convexity.StdSimplex.map _ (Convexity.StdSimplex.map _ t)) = _
  rw [← Convexity.StdSimplex.map_comp]
  rfl

private theorem ccm17_shuffle_back_projection {n : ℕ} (s : ccm17_Shuffle n) :
    (TopCat.toSSet.map (TopCat.ofHom
      (⟨Prod.snd, continuous_snd⟩ : C((Fin 2 → ℝ) × (Fin n → ℝ), Fin n → ℝ)))).app _
      (backFace _ (p := 2) (q := n) (ccm17_shuffleSimplex s)) =
    ccm17_affineReparam (fun i : Fin (n + 1) =>
      ccm17_shuffleRight s ⟨2 + i.val, by omega⟩) := by
  apply ((TopCat.of (Fin n → ℝ)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  change standardAffineSimplex n
    (Convexity.StdSimplex.map _ (Convexity.StdSimplex.map _ t)) = _
  rw [← Convexity.StdSimplex.map_comp]
  rfl

#print axioms ccm17_shuffle_front_projection
#print axioms ccm17_shuffle_back_projection

private theorem ccm17_affineReparam_id (d : ℕ) :
    ccm17_affineReparam (id : Fin (d + 1) → Fin (d + 1)) =
      standardSingularSimplex d := by
  apply ((TopCat.of (Fin d → ℝ)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  change standardAffineSimplex d (Convexity.StdSimplex.map id t) = _
  rw [Convexity.StdSimplex.map_id]
  rfl

private theorem ccm17_identityShuffle_front (n : ℕ) :
    (fun i : Fin 3 => ccm17_shuffleLeft (ccm17_identityShuffle n)
      ⟨i.val, by omega⟩) = id := by
  funext i
  apply Fin.ext
  simp only [ccm17_shuffleLeft, ccm17_identityShuffle, Function.id_def]
  split_ifs <;> omega

private theorem ccm17_identityShuffle_back (n : ℕ) :
    (fun i : Fin (n + 1) => ccm17_shuffleRight (ccm17_identityShuffle n)
      ⟨2 + i.val, by omega⟩) = id := by
  funext i
  apply Fin.ext
  simp only [ccm17_shuffleRight, ccm17_shuffleLeft, ccm17_identityShuffle,
    Function.id_def]
  split_ifs <;> omega

#print axioms ccm17_affineReparam_id
#print axioms ccm17_identityShuffle_front
#print axioms ccm17_identityShuffle_back

/-- The ambient product cochain pulled back from the two punctured factors. -/
private def ccm17_productCochain (n : ℕ)
    (u : RelativeCochain ℚ (puncturedPair ℝ 2) 2)
    (v : RelativeCochain ℚ (puncturedPair ℝ n) n) :=
  cupCochain (TopCat.of ((Fin 2 → ℝ) × (Fin n → ℝ))) 2 n
    (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom
      (⟨Prod.fst, continuous_fst⟩ : C((Fin 2 → ℝ) × (Fin n → ℝ), Fin 2 → ℝ)))) 2
      (relativeCochainToAbsolute ℚ (puncturedPair ℝ 2) 2 u))
    (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom
      (⟨Prod.snd, continuous_snd⟩ : C((Fin 2 → ℝ) × (Fin n → ℝ), Fin n → ℝ)))) n
      (relativeCochainToAbsolute ℚ (puncturedPair ℝ n) n v))

/-- Only the ordered shuffle contributes to the Alexander–Whitney evaluation.
The other front faces avoid the left origin. -/
private theorem ccm17_productCochain_shuffle (n : ℕ)
    (u : RelativeCochain ℚ (puncturedPair ℝ 2) 2)
    (v : RelativeCochain ℚ (puncturedPair ℝ n) n) (s : ccm17_Shuffle n) :
    ccm17_productCochain n u v (chainOfSimplex ℚ (ccm17_shuffleSimplex s)) =
      if s = ccm17_identityShuffle n then
        relativeCochainToAbsolute ℚ (puncturedPair ℝ 2) 2 u
          (chainOfSimplex ℚ (standardSingularSimplex 2)) *
        relativeCochainToAbsolute ℚ (puncturedPair ℝ n) n v
          (chainOfSimplex ℚ (standardSingularSimplex n))
      else 0 := by
  classical
  simp only [ccm17_productCochain, cupCochain_apply_simplex,
    cochainMap_apply, chainOfSimplex_map]
  rw [ccm17_shuffle_front_projection, ccm17_shuffle_back_projection]
  split_ifs with hs
  · subst s
    rw [ccm17_identityShuffle_front, ccm17_identityShuffle_back,
      ccm17_affineReparam_id, ccm17_affineReparam_id]
    rfl
  · exact (congrArg (fun a : ℚ => a * _)
      (ccm17_affineReparam_evaluation_zero _ (Fin.last 2)
        (ccm17_shuffleLeft_front_omit s hs) u)).trans (zero_mul _)

#print axioms ccm17_productCochain_shuffle

/-- The signed `(2,n)` affine shuffle chain, with the left factor first.
The exponent counts right steps preceding the two left steps. -/
private def ccm17_shuffleChain (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of ((Fin 2 → ℝ) × (Fin n → ℝ)))).chainComplex
      (ModuleCat.of ℚ ℚ)).X (2 + n) :=
  ∑ s : ccm17_Shuffle n,
    (-1 : ℚ) ^ (s.1.1.val + s.1.2.val - 1) • chainOfSimplex ℚ (ccm17_shuffleSimplex s)

/-- The signed shuffle sum evaluates to the product of the two fixed affine
simplex evaluations, including when the right factor has dimension zero. -/
private theorem ccm17_productCochain_shuffleChain (n : ℕ)
    (u : RelativeCochain ℚ (puncturedPair ℝ 2) 2)
    (v : RelativeCochain ℚ (puncturedPair ℝ n) n) :
    ccm17_productCochain n u v (ccm17_shuffleChain n) =
      relativeCochainToAbsolute ℚ (puncturedPair ℝ 2) 2 u
        (chainOfSimplex ℚ (standardSingularSimplex 2)) *
      relativeCochainToAbsolute ℚ (puncturedPair ℝ n) n v
        (chainOfSimplex ℚ (standardSingularSimplex n)) := by
  classical
  simp only [ccm17_shuffleChain, map_sum, map_smul, smul_eq_mul,
    ccm17_productCochain_shuffle]
  rw [Finset.sum_eq_single (ccm17_identityShuffle n)]
  · simp only [ccm17_identityShuffle, ↓reduceIte, Nat.reduceAdd,
      Nat.reduceSub, pow_zero, one_mul]
  · intro s _ hs
    rw [if_neg hs, mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

#print axioms ccm17_productCochain_shuffleChain

/-- Representatives of both independently normalized complex coclasses give
value one on the real signed shuffle chain after splitting complex coordinates. -/
private theorem ccm17_normalized_shuffle_evaluation (q : ℕ) :
    ∃ u : (RelativeCochainComplex ℚ (puncturedPair ℂ 1)).cycles 2,
    ∃ v : (RelativeCochainComplex ℚ (puncturedPair ℂ q)).cycles (q * 2),
      (RelativeCochainComplex ℚ (puncturedPair ℂ 1)).homologyπ 2 u =
        normalizedPointCoclass 1 ∧
      (RelativeCochainComplex ℚ (puncturedPair ℂ q)).homologyπ (q * 2) v =
        (Nat.mul_comm q 2).symm ▸ normalizedPointCoclass q ∧
      ccm17_productCochain (q * 2)
        ((relativeCochainComplexMap ℚ (standardComplexRealPairIso 1).inv).f 2
          ((RelativeCochainComplex ℚ (puncturedPair ℂ 1)).iCycles 2 u))
        ((relativeCochainComplexMap ℚ (standardComplexRealPairIso q).inv).f (q * 2)
          ((RelativeCochainComplex ℚ (puncturedPair ℂ q)).iCycles (q * 2) v))
        (ccm17_shuffleChain (q * 2)) = 1 := by
  obtain ⟨u, hu, heu⟩ := ccm17_normalizedPointCoclass_representative 1
  obtain ⟨v, hv, hev⟩ := ccm17_normalizedPointCoclass_representative q
  refine ⟨u, v, hu, hv, ?_⟩
  exact (ccm17_productCochain_shuffleChain _ _ _).trans
    ((congrArg₂ (fun a b : ℚ => a * b) heu hev).trans (one_mul 1))

#print axioms ccm17_normalized_shuffle_evaluation

/-- Join the real coordinates of the divisor factor and the remaining complex
normal coordinates in their prescribed order. -/
private def ccm17_complexBlock (q : ℕ) :
    C((Fin 2 → ℝ) × (Fin (q * 2) → ℝ), Fin (q + 1) → ℂ) where
  toFun t := Fin.cons ((complexRealHomeomorph 1).symm t.1 0)
    ((complexRealHomeomorph q).symm t.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> fun_prop

private theorem ccm17_complexBlock_head (q : ℕ)
    (t : (Fin 2 → ℝ) × (Fin (q * 2) → ℝ)) :
    ccm17_head q (ccm17_complexBlock q t) = (complexRealHomeomorph 1).symm t.1 := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

private theorem ccm17_complexBlock_tail (q : ℕ)
    (t : (Fin 2 → ℝ) × (Fin (q * 2) → ℝ)) :
    ccm17_tail q (ccm17_complexBlock q t) = (complexRealHomeomorph q).symm t.2 := by
  funext i
  rfl

/-- The explicit signed shuffle chain transported into the coordinate normal space. -/
private def ccm17_complexShuffleChain (q : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of (Fin (q + 1) → ℂ))).chainComplex
      (ModuleCat.of ℚ ℚ)).X (2 + q * 2) :=
  ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (ccm17_complexBlock q)))
    (ModuleCat.of ℚ ℚ)).f (2 + q * 2)).hom (ccm17_shuffleChain (q * 2))

#print axioms ccm17_complexBlock_head
#print axioms ccm17_complexBlock_tail
#print axioms ccm17_complexShuffleChain

/-- The ordered block map is a homeomorphism, with inverse obtained by the
head and tail projections followed by consecutive real and imaginary coordinates. -/
private def ccm17_complexBlockHomeomorph (q : ℕ) :
    ((Fin 2 → ℝ) × (Fin (q * 2) → ℝ)) ≃ₜ (Fin (q + 1) → ℂ) where
  toFun := ccm17_complexBlock q
  invFun z := ((complexRealHomeomorph 1) (ccm17_head q z),
    (complexRealHomeomorph q) (ccm17_tail q z))
  left_inv t := by
    simp only [ccm17_complexBlock_head, ccm17_complexBlock_tail,
      Homeomorph.apply_symm_apply]
  right_inv z := by
    change Fin.cons
      ((complexRealHomeomorph 1).symm ((complexRealHomeomorph 1) (ccm17_head q z)) 0)
      ((complexRealHomeomorph q).symm ((complexRealHomeomorph q) (ccm17_tail q z))) = z
    simp only [Homeomorph.symm_apply_apply]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  continuous_toFun := (ccm17_complexBlock q).continuous
  continuous_invFun := by fun_prop

#print axioms ccm17_complexBlockHomeomorph

private theorem ccm17_cochainMap_comp {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (u : Cochain ℚ (TopCat.toSSet.obj Z) n) :
    cochainMap ℚ (TopCat.toSSet.map f) n
      (cochainMap ℚ (TopCat.toSSet.map g) n u) =
    cochainMap ℚ (TopCat.toSSet.map (f ≫ g)) n u := by
  ext c
  simp only [cochainMap_apply, Functor.map_comp, SSet.chainComplexMap,
    HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]

#print axioms ccm17_cochainMap_comp

/-- Pullback of an absolute cochain from a complex normal factor through a
real parametrization of the normal coordinates. -/
private theorem ccm17_normal_absolute_transport
    (X Y : TopCat.{0}) (c n : ℕ) (f : C(Y, Fin c → ℂ))
    (g : C(X, Y)) (r : C(X, Fin (c * 2) → ℝ))
    (h : f.comp g = (⟨(complexRealHomeomorph c).symm, (complexRealHomeomorph c).symm.continuous⟩ : C(Fin (c * 2) → ℝ, Fin c → ℂ)).comp r)
    (u : RelativeCochain ℚ (puncturedPair ℂ c) n) :
    cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom g)) n
      (relativeCochainToAbsolute ℚ
        (TopPair.ofSubset (ccm17_zeroSupport Y c f : Set Y)ᶜ) n
        ((relativeCochainComplexMap ℚ (ccm17_normalPair Y c f)).f n u)) =
    cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom r)) n
      (relativeCochainToAbsolute ℚ (puncturedPair ℝ (c * 2)) n
        ((relativeCochainComplexMap ℚ (standardComplexRealPairIso c).inv).f n u)) := by
  let k : C(Fin (c * 2) → ℝ, Fin c → ℂ) :=
    ⟨(complexRealHomeomorph c).symm, (complexRealHomeomorph c).symm.continuous⟩
  let a := relativeCochainToAbsolute ℚ (puncturedPair ℂ c) n u
  calc
    _ = cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom g)) n
        (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom f)) n a) :=
      congrArg (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom g)) n)
        (ccm17_absolute_pullback (ccm17_normalPair Y c f) n u)
    _ = cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom (f.comp g))) n a :=
      ccm17_cochainMap_comp (TopCat.ofHom g) (TopCat.ofHom f) n a
    _ = cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom (k.comp r))) n a := by
      rw [h]
    _ = cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom r)) n
        (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom k)) n a) :=
      (ccm17_cochainMap_comp (TopCat.ofHom r) (TopCat.ofHom k) n a).symm
    _ = _ := congrArg (cochainMap ℚ (TopCat.toSSet.map (TopCat.ofHom r)) n)
      (ccm17_absolute_pullback (standardComplexRealPairIso c).inv n u).symm

#print axioms ccm17_normal_absolute_transport

/-- The actual relative cup lift on the transported shuffle chain is the real
product cochain, with both normal-coordinate pullbacks accounted for. -/
private theorem ccm17_relativeCupLift_complexShuffle (q : ℕ)
    (u : RelativeCochain ℚ (puncturedPair ℂ 1) 2)
    (v : RelativeCochain ℚ (puncturedPair ℂ q) (q * 2)) :
    ccm13_relativeCupLift (TopCat.of (Fin (q + 1) → ℂ))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q)) 2 (q * 2)
      ((relativeCochainComplexMap ℚ
        (ccm17_normalPair (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))).f 2 u)
      ((relativeCochainComplexMap ℚ
        (ccm17_normalPair (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q))).f (q * 2) v)
      (ccm17_complexShuffleChain q) =
    ccm17_productCochain (q * 2)
      ((relativeCochainComplexMap ℚ (standardComplexRealPairIso 1).inv).f 2 u)
      ((relativeCochainComplexMap ℚ (standardComplexRealPairIso q).inv).f (q * 2) v)
      (ccm17_shuffleChain (q * 2)) := by
  unfold ccm13_relativeCupLift ccm17_complexShuffleChain
  rw [← cochainMap_apply, cupCochain_naturality]
  have hh : (ccm17_head q).comp (ccm17_complexBlock q) =
      (⟨(complexRealHomeomorph 1).symm, (complexRealHomeomorph 1).symm.continuous⟩ :
        C(Fin 2 → ℝ, Fin 1 → ℂ)).comp ⟨Prod.fst, continuous_fst⟩ := by
    ext t i
    exact congrFun (ccm17_complexBlock_head q t) i
  have ht : (ccm17_tail q).comp (ccm17_complexBlock q) =
      (⟨(complexRealHomeomorph q).symm, (complexRealHomeomorph q).symm.continuous⟩ :
        C(Fin (q * 2) → ℝ, Fin q → ℂ)).comp ⟨Prod.snd, continuous_snd⟩ := by
    ext t i
    exact congrFun (ccm17_complexBlock_tail q t) i
  have hhead := ccm17_normal_absolute_transport
    (TopCat.of ((Fin 2 → ℝ) × (Fin (q * 2) → ℝ)))
    (TopCat.of (Fin (q + 1) → ℂ)) 1 2 (ccm17_head q) (ccm17_complexBlock q)
    ⟨Prod.fst, continuous_fst⟩ hh u
  have htail := ccm17_normal_absolute_transport
    (TopCat.of ((Fin 2 → ℝ) × (Fin (q * 2) → ℝ)))
    (TopCat.of (Fin (q + 1) → ℂ)) q (q * 2) (ccm17_tail q) (ccm17_complexBlock q)
    ⟨Prod.snd, continuous_snd⟩ ht v
  exact congrArg₂ (fun a b =>
    cupCochain (TopCat.of ((Fin 2 → ℝ) × (Fin (q * 2) → ℝ)))
      2 (q * 2) a b (ccm17_shuffleChain (q * 2))) hhead htail

#print axioms ccm17_relativeCupLift_complexShuffle

/-- The normalized factor cocycles evaluate to one on the actual complex
shuffle chain through the relative cup lift. -/
private theorem ccm17_normalized_complexShuffle_evaluation (q : ℕ) :
    ∃ u : (RelativeCochainComplex ℚ (puncturedPair ℂ 1)).cycles 2,
    ∃ v : (RelativeCochainComplex ℚ (puncturedPair ℂ q)).cycles (q * 2),
      (RelativeCochainComplex ℚ (puncturedPair ℂ 1)).homologyπ 2 u =
        normalizedPointCoclass 1 ∧
      (RelativeCochainComplex ℚ (puncturedPair ℂ q)).homologyπ (q * 2) v =
        (Nat.mul_comm q 2).symm ▸ normalizedPointCoclass q ∧
      ccm13_relativeCupLift (TopCat.of (Fin (q + 1) → ℂ))
        (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
        (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q)) 2 (q * 2)
        ((relativeCochainComplexMap ℚ
          (ccm17_normalPair (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))).f 2
          ((RelativeCochainComplex ℚ (puncturedPair ℂ 1)).iCycles 2 u))
        ((relativeCochainComplexMap ℚ
          (ccm17_normalPair (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q))).f (q * 2)
          ((RelativeCochainComplex ℚ (puncturedPair ℂ q)).iCycles (q * 2) v))
        (ccm17_complexShuffleChain q) = 1 := by
  obtain ⟨u, v, hu, hv, he⟩ := ccm17_normalized_shuffle_evaluation q
  exact ⟨u, v, hu, hv, (ccm17_relativeCupLift_complexShuffle q _ _).trans he⟩

#print axioms ccm17_normalized_complexShuffle_evaluation

/-- Simultaneous transport of the second cochain and the total chain degree
leaves the cup evaluation unchanged. -/
private theorem ccm17_relativeCupLift_degree_cast (Y : TopCat.{0}) (S T : Set Y)
    (p : ℕ) {m n : ℕ} (h : m = n)
    (u : RelativeCochain ℚ (TopPair.ofSubset Sᶜ) p)
    (v : RelativeCochain ℚ (TopPair.ofSubset Tᶜ) m)
    (z : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X (p + m)) :
    ccm13_relativeCupLift Y S T p n u (h ▸ v)
      ((congrArg (p + ·) h) ▸ z) = ccm13_relativeCupLift Y S T p m u v z := by
  subst n
  rfl

#print axioms ccm17_relativeCupLift_degree_cast

/-- The complex shuffle chain at the degree used by the frozen cup product. -/
private def ccm17_complexShuffleChainCast (q : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of (Fin (q + 1) → ℂ))).chainComplex
      (ModuleCat.of ℚ ℚ)).X (2 + 2 * q) :=
  (congrArg (2 + ·) (Nat.mul_comm q 2)) ▸ ccm17_complexShuffleChain q

/-- The same product evaluation in degree `2 + 2*q`, including the cochain
transport from degree `q*2` to degree `2*q`. -/
private theorem ccm17_relativeCupLift_complexShuffle_cast (q : ℕ)
    (u : RelativeCochain ℚ (puncturedPair ℂ 1) 2)
    (v : RelativeCochain ℚ (puncturedPair ℂ q) (q * 2)) :
    ccm13_relativeCupLift (TopCat.of (Fin (q + 1) → ℂ))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q)) 2 (2 * q)
      ((relativeCochainComplexMap ℚ
        (ccm17_normalPair (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))).f 2 u)
      ((Nat.mul_comm q 2) ▸ ((relativeCochainComplexMap ℚ
        (ccm17_normalPair (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q))).f (q * 2) v))
      (ccm17_complexShuffleChainCast q) =
    ccm17_productCochain (q * 2)
      ((relativeCochainComplexMap ℚ (standardComplexRealPairIso 1).inv).f 2 u)
      ((relativeCochainComplexMap ℚ (standardComplexRealPairIso q).inv).f (q * 2) v)
      (ccm17_shuffleChain (q * 2)) := by
  exact (ccm17_relativeCupLift_degree_cast _ _ _ 2 (Nat.mul_comm q 2)
    _ _ (ccm17_complexShuffleChain q)).trans
      (ccm17_relativeCupLift_complexShuffle q u v)

#print axioms ccm17_relativeCupLift_complexShuffle_cast

open scoped Simplicial in
/-- A simplex lying in either complement maps to zero in the small quotient. -/
private theorem ccm17_smallProjection_simplex_zero (Y : TopCat.{0})
    (S T : Set Y) {n : ℕ} (σ : (TopCat.toSSet.obj Y) _⦋n⦌)
    (hσ : σ ∈ (coverSmallSingularSubcomplex Y (ccm13_complementFamily Y S T)).obj (.op (.mk n))) :
    ((ccm14_smallProjection Y S T).f n).hom (chainOfSimplex ℚ σ) = 0 := by
  let τ : (coverSmallSingularSubcomplex Y (ccm13_complementFamily Y S T) : SSet) _⦋n⦌ :=
    ⟨σ, hσ⟩
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) (cokernel.condition (ccm14_smallInclusion Y S T)))
    (chainOfSimplex ℚ τ)
  change ((ccm14_smallProjection Y S T).f n).hom
    (((ccm14_smallInclusion Y S T).f n).hom (chainOfSimplex ℚ τ)) = 0 at h
  have hi : (coverSmallSingularSubcomplex Y
      (ccm13_complementFamily Y S T)).ι.app _ τ = σ := rfl
  simpa only [ccm14_smallInclusion, coverSmallRationalSingularChainInclusion,
    chainOfSimplex_map, hi] using h

#print axioms ccm17_smallProjection_simplex_zero

open scoped Simplicial in
/-- Range containment in one complement suffices to kill a simplex in the
small relative quotient. -/
private theorem ccm17_smallProjection_simplex_zero_of_range (Y : TopCat.{0})
    (S T : Set Y) {n : ℕ} (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (b : Bool)
    (hσ : ∀ t, Y.toSSetObjEquiv _ σ t ∈ ccm13_complementFamily Y S T b) :
    ((ccm14_smallProjection Y S T).f n).hom (chainOfSimplex ℚ σ) = 0 := by
  apply ccm17_smallProjection_simplex_zero
  apply (mem_coverSmallSingularSubcomplex_iff_exists_preimage Y _ σ).mpr
  let τ := ((TopCat.of (ccm13_complementFamily Y S T b)).toSSetObjEquiv _).symm
    ⟨fun t => ⟨Y.toSSetObjEquiv _ σ t, hσ t⟩, by fun_prop⟩
  refine ⟨b, τ, ?_⟩
  apply (Y.toSSetObjEquiv _).injective
  rfl

#print axioms ccm17_smallProjection_simplex_zero_of_range

open scoped Simplicial in
open Convexity in
/-- A product affine simplex in complex block coordinates, with arbitrary
vertex maps on its two factors. -/
private def ccm17_complexProductSimplex (q : ℕ) {m : ℕ}
    (a : Fin (m + 1) → Fin 3) (b : Fin (m + 1) → Fin (q * 2 + 1)) :
    (TopCat.toSSet.obj (TopCat.of (Fin (q + 1) → ℂ))) _⦋m⦌ :=
  ((TopCat.of (Fin (q + 1) → ℂ)).toSSetObjEquiv _).symm
    ⟨fun t => ccm17_complexBlock q
      (standardAffineSimplex 2 (StdSimplex.map a t),
        standardAffineSimplex (q * 2) (StdSimplex.map b t)), by fun_prop⟩

open scoped Simplicial in
/-- A face acts on both vertex maps of an affine product simplex. -/
private theorem ccm17_complexProductSimplex_face (q m : ℕ)
    (a : Fin (m + 2) → Fin 3) (b : Fin (m + 2) → Fin (q * 2 + 1))
    (i : Fin (m + 2)) :
    (TopCat.toSSet.obj (TopCat.of (Fin (q + 1) → ℂ))).δ i
      (ccm17_complexProductSimplex q a b) =
    ccm17_complexProductSimplex q (a ∘ i.succAbove) (b ∘ i.succAbove) := by
  apply ((TopCat.of (Fin (q + 1) → ℂ)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  change ccm17_complexBlock q
    (standardAffineSimplex 2 (Convexity.StdSimplex.map a (Convexity.StdSimplex.map _ t)),
      standardAffineSimplex (q * 2) (Convexity.StdSimplex.map b (Convexity.StdSimplex.map _ t))) = _
  rw [← Convexity.StdSimplex.map_comp, ← Convexity.StdSimplex.map_comp]
  rfl

#print axioms ccm17_complexProductSimplex_face

/-- Omitting a left vertex puts the entire product simplex in the head
complement, so its image in the small relative complex is zero. -/
private theorem ccm17_complexProductSimplex_left_zero (q : ℕ) {m : ℕ}
    (a : Fin (m + 1) → Fin 3) (b : Fin (m + 1) → Fin (q * 2 + 1))
    (j : Fin 3) (hj : ∀ i, a i ≠ j) :
    ((ccm14_smallProjection (TopCat.of (Fin (q + 1) → ℂ))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q))).f m).hom
      (chainOfSimplex ℚ (ccm17_complexProductSimplex q a b)) = 0 := by
  apply ccm17_smallProjection_simplex_zero_of_range _ _ _ _ false
  intro t
  change ccm17_head q (ccm17_complexBlock q _) ≠ 0
  rw [ccm17_complexBlock_head]
  intro hz
  have he := congrArg (complexRealHomeomorph 1) hz
  rw [Homeomorph.apply_symm_apply] at he
  have hz0 : complexRealHomeomorph 1 0 = 0 := (Complex.piCoordCLE 1).map_zero
  rw [hz0] at he
  exact ccm17_affine_reparam_ne_zero a j hj t he

#print axioms ccm17_complexProductSimplex_left_zero

/-- Omitting a right vertex puts the entire product simplex in the tail
complement, so its image in the small relative complex is zero. -/
private theorem ccm17_complexProductSimplex_right_zero (q : ℕ) {m : ℕ}
    (a : Fin (m + 1) → Fin 3) (b : Fin (m + 1) → Fin (q * 2 + 1))
    (j : Fin (q * 2 + 1)) (hj : ∀ i, b i ≠ j) :
    ((ccm14_smallProjection (TopCat.of (Fin (q + 1) → ℂ))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q))).f m).hom
      (chainOfSimplex ℚ (ccm17_complexProductSimplex q a b)) = 0 := by
  apply ccm17_smallProjection_simplex_zero_of_range _ _ _ _ true
  intro t
  change ccm17_tail q (ccm17_complexBlock q _) ≠ 0
  rw [ccm17_complexBlock_tail]
  intro hz
  have he := congrArg (complexRealHomeomorph q) hz
  rw [Homeomorph.apply_symm_apply] at he
  have hz0 : complexRealHomeomorph q 0 = 0 := (Complex.piCoordCLE q).map_zero
  rw [hz0] at he
  exact ccm17_affine_reparam_ne_zero b j hj t he

#print axioms ccm17_complexProductSimplex_right_zero

/-- If a shuffle starts with a left step, deleting its first vertex omits
vertex zero in the left factor. -/
private theorem ccm17_shuffle_first_left_omit {n : ℕ} (s : ccm17_Shuffle n)
    (hs : s.1.1.val = 0) (i : Fin (2 + n)) :
    ccm17_shuffleLeft s i.succ ≠ 0 := by
  intro he
  have hv := congrArg Fin.val he
  simp only [ccm17_shuffleLeft, Fin.val_succ, Fin.val_zero, hs] at hv
  split_ifs at hv <;> omega

/-- If a shuffle starts with a right step, deleting its first vertex omits
vertex zero in the right factor. -/
private theorem ccm17_shuffle_first_right_omit {n : ℕ} (s : ccm17_Shuffle n)
    (hs : s.1.1.val ≠ 0) (i : Fin (2 + n)) :
    ccm17_shuffleRight s i.succ ≠ 0 := by
  have hab : s.1.1.val < s.1.2.val := s.2
  intro he
  have hv := congrArg Fin.val he
  simp only [ccm17_shuffleRight, ccm17_shuffleLeft, Fin.val_succ, Fin.val_zero] at hv
  split_ifs at hv <;> omega

/-- If a shuffle ends with a left step, deleting its last vertex omits
the last vertex of the left factor. -/
private theorem ccm17_shuffle_last_left_omit {n : ℕ} (s : ccm17_Shuffle n)
    (hs : s.1.2.val = n + 1) (i : Fin (2 + n)) :
    ccm17_shuffleLeft s i.castSucc ≠ Fin.last 2 := by
  intro he
  have hv := congrArg Fin.val he
  simp only [ccm17_shuffleLeft, Fin.val_castSucc, Fin.val_last, hs] at hv
  split_ifs at hv <;> omega

/-- If a shuffle ends with a right step, deleting its last vertex omits
the last vertex of the right factor. -/
private theorem ccm17_shuffle_last_right_omit {n : ℕ} (s : ccm17_Shuffle n)
    (hs : s.1.2.val ≠ n + 1) (i : Fin (2 + n)) :
    ccm17_shuffleRight s i.castSucc ≠ Fin.last n := by
  have hab : s.1.1.val < s.1.2.val := s.2
  have hb := s.1.2.isLt
  intro he
  have hv := congrArg Fin.val he
  simp only [ccm17_shuffleRight, ccm17_shuffleLeft, Fin.val_castSucc, Fin.val_last] at hv
  split_ifs at hv <;> omega

#print axioms ccm17_shuffle_first_left_omit
#print axioms ccm17_shuffle_first_right_omit
#print axioms ccm17_shuffle_last_left_omit
#print axioms ccm17_shuffle_last_right_omit

/-- Between consecutive left steps, deleting the middle vertex omits the
middle left-factor vertex. -/
private theorem ccm17_shuffle_consecutive_left_omit {n : ℕ} (s : ccm17_Shuffle n)
    (hs : s.1.2.val = s.1.1.val + 1) (i : Fin (2 + n + 1))
    (hi : i.val = s.1.2.val) (j : Fin (2 + n)) :
    ccm17_shuffleLeft s (i.succAbove j) ≠ 1 := by
  have hne : (i.succAbove j).val ≠ i.val := by
    intro h
    exact Fin.succAbove_ne i j (Fin.ext h)
  intro he
  have hv := congrArg Fin.val he
  simp only [ccm17_shuffleLeft, Fin.val_one] at hv
  split_ifs at hv <;> omega

/-- At a vertex flanked by right steps, deleting the vertex omits its
right-factor vertex. -/
private theorem ccm17_shuffle_consecutive_right_omit {n : ℕ} (s : ccm17_Shuffle n)
    (i : Fin (2 + n + 1))
    (ha : i.val ≠ s.1.1.val) (ha' : i.val ≠ s.1.1.val + 1)
    (hb : i.val ≠ s.1.2.val) (hb' : i.val ≠ s.1.2.val + 1)
    (j : Fin (2 + n)) :
    ccm17_shuffleRight s (i.succAbove j) ≠ ccm17_shuffleRight s i := by
  have hne : (i.succAbove j).val ≠ i.val := by
    intro h
    exact Fin.succAbove_ne i j (Fin.ext h)
  have hab : s.1.1.val < s.1.2.val := s.2
  intro he
  have hv := congrArg Fin.val he
  simp only [ccm17_shuffleRight, ccm17_shuffleLeft] at hv
  split_ifs at hv <;> omega

#print axioms ccm17_shuffle_consecutive_left_omit
#print axioms ccm17_shuffle_consecutive_right_omit

/-- Moving the first left step across a neighboring right step does not change
the product face obtained by deleting their common vertex. -/
private theorem ccm17_shuffle_move_first_face {n : ℕ} (s t : ccm17_Shuffle n)
    (ha : t.1.1.val = s.1.1.val + 1) (hb : t.1.2 = s.1.2)
    (i : Fin (2 + n + 1)) (hi : i.val = s.1.1.val + 1) :
    (fun j => ccm17_shuffleLeft s (i.succAbove j)) =
      (fun j => ccm17_shuffleLeft t (i.succAbove j)) ∧
    (fun j => ccm17_shuffleRight s (i.succAbove j)) =
      (fun j => ccm17_shuffleRight t (i.succAbove j)) := by
  have hl : (fun j => ccm17_shuffleLeft s (i.succAbove j)) =
      (fun j => ccm17_shuffleLeft t (i.succAbove j)) := by
    funext j
    have hne : (i.succAbove j).val ≠ i.val := by
      intro h
      exact Fin.succAbove_ne i j (Fin.ext h)
    apply Fin.ext
    simp only [ccm17_shuffleLeft, ha, hb]
    split_ifs <;> omega
  refine ⟨hl, ?_⟩
  funext j
  apply Fin.ext
  change (i.succAbove j).val - (ccm17_shuffleLeft s (i.succAbove j)).val =
    (i.succAbove j).val - (ccm17_shuffleLeft t (i.succAbove j)).val
  rw [congrFun hl j]

/-- The analogous face identity when the second left step moves across a
neighboring right step. -/
private theorem ccm17_shuffle_move_second_face {n : ℕ} (s t : ccm17_Shuffle n)
    (ha : t.1.1 = s.1.1) (hb : t.1.2.val = s.1.2.val + 1)
    (i : Fin (2 + n + 1)) (hi : i.val = s.1.2.val + 1) :
    (fun j => ccm17_shuffleLeft s (i.succAbove j)) =
      (fun j => ccm17_shuffleLeft t (i.succAbove j)) ∧
    (fun j => ccm17_shuffleRight s (i.succAbove j)) =
      (fun j => ccm17_shuffleRight t (i.succAbove j)) := by
  have hl : (fun j => ccm17_shuffleLeft s (i.succAbove j)) =
      (fun j => ccm17_shuffleLeft t (i.succAbove j)) := by
    funext j
    have hne : (i.succAbove j).val ≠ i.val := by
      intro h
      exact Fin.succAbove_ne i j (Fin.ext h)
    apply Fin.ext
    simp only [ccm17_shuffleLeft, ha, hb]
    split_ifs <;> omega
  refine ⟨hl, ?_⟩
  funext j
  apply Fin.ext
  change (i.succAbove j).val - (ccm17_shuffleLeft s (i.succAbove j)).val =
    (i.succAbove j).val - (ccm17_shuffleLeft t (i.succAbove j)).val
  rw [congrFun hl j]

#print axioms ccm17_shuffle_move_first_face
#print axioms ccm17_shuffle_move_second_face

/-- Sliding either left step one place right reverses the shuffle sign. -/
private theorem ccm17_shuffle_sign_slide {n : ℕ} (s t : ccm17_Shuffle n)
    (h : t.1.1.val + t.1.2.val = s.1.1.val + s.1.2.val + 1) :
    (-1 : ℚ) ^ (t.1.1.val + t.1.2.val - 1) =
      -((-1 : ℚ) ^ (s.1.1.val + s.1.2.val - 1)) := by
  have hs : s.1.1.val < s.1.2.val := s.2
  have he : t.1.1.val + t.1.2.val - 1 = (s.1.1.val + s.1.2.val - 1) + 1 := by
    omega
  rw [he, pow_succ, mul_neg_one]

#print axioms ccm17_shuffle_sign_slide

/-- Interchange two adjacent step positions and sort the two left positions. -/
private def ccm17_swapShuffle {n : ℕ} (k : Fin (n + 1))
    (s : ccm17_Shuffle n) : ccm17_Shuffle n := by
  let e := Equiv.swap k.castSucc k.succ
  let a := e s.1.1
  let b := e s.1.2
  have hab : a ≠ b := fun h => (ne_of_lt s.2) (e.injective h)
  exact if h : a < b then ⟨(a, b), h⟩ else
    ⟨(b, a), lt_of_le_of_ne (le_of_not_gt h) hab.symm⟩

private theorem ccm17_swapShuffle_involutive {n : ℕ} (k : Fin (n + 1)) :
    Function.Involutive (ccm17_swapShuffle k) := by
  intro s
  unfold ccm17_swapShuffle
  dsimp only
  split_ifs with h h' h'
  all_goals apply Subtype.ext; apply Prod.ext
  all_goals simp only [Prod.fst, Prod.snd, Equiv.swap_apply_self]
  all_goals simp_all [not_lt_of_gt s.2, s.2]

#print axioms ccm17_swapShuffle_involutive

/-- A face of a complex shuffle simplex, projected to the small quotient.
The vertex cast only reassociates the natural-number dimension. -/
private def ccm17_smallShuffleFace (q : ℕ) (s : ccm17_Shuffle (q * 2))
    (i : Fin (2 + q * 2 + 1)) :
    (ccm14_smallRelativeComplex (TopCat.of (Fin (q + 1) → ℂ))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q))).X (q * 2 + 1) :=
  ((ccm14_smallProjection (TopCat.of (Fin (q + 1) → ℂ))
    (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
    (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q))).f (q * 2 + 1)).hom
    (chainOfSimplex ℚ (ccm17_complexProductSimplex q
      (fun j : Fin (q * 2 + 1 + 1) => ccm17_shuffleLeft s (i.succAbove ⟨j.val, by omega⟩))
      (fun j : Fin (q * 2 + 1 + 1) => ccm17_shuffleRight s (i.succAbove ⟨j.val, by omega⟩))))

private theorem ccm17_smallShuffleFace_left_zero (q : ℕ)
    (s : ccm17_Shuffle (q * 2)) (i : Fin (2 + q * 2 + 1)) (a : Fin 3)
    (h : ∀ j, ccm17_shuffleLeft s (i.succAbove j) ≠ a) :
    ccm17_smallShuffleFace q s i = 0 :=
  ccm17_complexProductSimplex_left_zero q _ _ a (fun j => h _)

private theorem ccm17_smallShuffleFace_right_zero (q : ℕ)
    (s : ccm17_Shuffle (q * 2)) (i : Fin (2 + q * 2 + 1)) (a : Fin (q * 2 + 1))
    (h : ∀ j, ccm17_shuffleRight s (i.succAbove j) ≠ a) :
    ccm17_smallShuffleFace q s i = 0 :=
  ccm17_complexProductSimplex_right_zero q _ _ a (fun j => h _)

private theorem ccm17_smallShuffleFace_eq (q : ℕ)
    (s t : ccm17_Shuffle (q * 2)) (i : Fin (2 + q * 2 + 1))
    (hl : (fun j => ccm17_shuffleLeft s (i.succAbove j)) =
      (fun j => ccm17_shuffleLeft t (i.succAbove j)))
    (hr : (fun j => ccm17_shuffleRight s (i.succAbove j)) =
      (fun j => ccm17_shuffleRight t (i.succAbove j))) :
    ccm17_smallShuffleFace q s i = ccm17_smallShuffleFace q t i := by
  unfold ccm17_smallShuffleFace
  have hl' : (fun j : Fin (q * 2 + 1 + 1) =>
      ccm17_shuffleLeft s (i.succAbove ⟨j.val, by omega⟩)) =
      (fun j : Fin (q * 2 + 1 + 1) =>
      ccm17_shuffleLeft t (i.succAbove ⟨j.val, by omega⟩)) := by
    funext j
    exact congrFun hl _
  have hr' : (fun j : Fin (q * 2 + 1 + 1) =>
      ccm17_shuffleRight s (i.succAbove ⟨j.val, by omega⟩)) =
      (fun j : Fin (q * 2 + 1 + 1) =>
      ccm17_shuffleRight t (i.succAbove ⟨j.val, by omega⟩)) := by
    funext j
    exact congrFun hr _
  rw [hl', hr']

/-- Paired mixed faces cancel as chains in the actual small quotient when
the first left step moves across the adjoining right step. -/
private theorem ccm17_smallShuffleFace_cancel_first (q : ℕ)
    (s t : ccm17_Shuffle (q * 2))
    (ha : t.1.1.val = s.1.1.val + 1) (hb : t.1.2 = s.1.2)
    (i : Fin (2 + q * 2 + 1)) (hi : i.val = s.1.1.val + 1) :
    (-1 : ℚ) ^ (s.1.1.val + s.1.2.val - 1) • ccm17_smallShuffleFace q s i +
      (-1 : ℚ) ^ (t.1.1.val + t.1.2.val - 1) • ccm17_smallShuffleFace q t i = 0 := by
  obtain ⟨hl, hr⟩ := ccm17_shuffle_move_first_face s t ha hb i hi
  rw [ccm17_smallShuffleFace_eq q s t i hl hr,
    ccm17_shuffle_sign_slide s t (by rw [ha, hb]; omega)]
  simp only [neg_smul, add_neg_cancel]

/-- Paired mixed faces also cancel when it is the second left step that moves. -/
private theorem ccm17_smallShuffleFace_cancel_second (q : ℕ)
    (s t : ccm17_Shuffle (q * 2))
    (ha : t.1.1 = s.1.1) (hb : t.1.2.val = s.1.2.val + 1)
    (i : Fin (2 + q * 2 + 1)) (hi : i.val = s.1.2.val + 1) :
    (-1 : ℚ) ^ (s.1.1.val + s.1.2.val - 1) • ccm17_smallShuffleFace q s i +
      (-1 : ℚ) ^ (t.1.1.val + t.1.2.val - 1) • ccm17_smallShuffleFace q t i = 0 := by
  obtain ⟨hl, hr⟩ := ccm17_shuffle_move_second_face s t ha hb i hi
  rw [ccm17_smallShuffleFace_eq q s t i hl hr,
    ccm17_shuffle_sign_slide s t (by rw [ha, hb]; omega)]
  simp only [neg_smul, add_neg_cancel]

#print axioms ccm17_smallShuffleFace_left_zero
#print axioms ccm17_smallShuffleFace_right_zero
#print axioms ccm17_smallShuffleFace_eq
#print axioms ccm17_smallShuffleFace_cancel_first
#print axioms ccm17_smallShuffleFace_cancel_second

private theorem ccm17_smallShuffleFace_first_zero (q : ℕ)
    (s : ccm17_Shuffle (q * 2)) : ccm17_smallShuffleFace q s 0 = 0 := by
  by_cases hs : s.1.1.val = 0
  · apply ccm17_smallShuffleFace_left_zero q s 0 0
    intro j
    simpa only [Fin.zero_succAbove] using ccm17_shuffle_first_left_omit s hs j
  · apply ccm17_smallShuffleFace_right_zero q s 0 0
    intro j
    simpa only [Fin.zero_succAbove] using ccm17_shuffle_first_right_omit s hs j

private theorem ccm17_smallShuffleFace_last_zero (q : ℕ)
    (s : ccm17_Shuffle (q * 2)) :
    ccm17_smallShuffleFace q s (Fin.last (2 + q * 2)) = 0 := by
  by_cases hs : s.1.2.val = q * 2 + 1
  · apply ccm17_smallShuffleFace_left_zero q s _ (Fin.last 2)
    intro j
    simpa only [Fin.succAbove_last] using ccm17_shuffle_last_left_omit s hs j
  · apply ccm17_smallShuffleFace_right_zero q s _ (Fin.last (q * 2))
    intro j
    simpa only [Fin.succAbove_last] using ccm17_shuffle_last_right_omit s hs j

private theorem ccm17_smallShuffleFace_consecutive_left_zero (q : ℕ)
    (s : ccm17_Shuffle (q * 2)) (hs : s.1.2.val = s.1.1.val + 1)
    (i : Fin (2 + q * 2 + 1)) (hi : i.val = s.1.2.val) :
    ccm17_smallShuffleFace q s i = 0 :=
  ccm17_smallShuffleFace_left_zero q s i 1
    (ccm17_shuffle_consecutive_left_omit s hs i hi)

private theorem ccm17_smallShuffleFace_consecutive_right_zero (q : ℕ)
    (s : ccm17_Shuffle (q * 2)) (i : Fin (2 + q * 2 + 1))
    (ha : i.val ≠ s.1.1.val) (ha' : i.val ≠ s.1.1.val + 1)
    (hb : i.val ≠ s.1.2.val) (hb' : i.val ≠ s.1.2.val + 1) :
    ccm17_smallShuffleFace q s i = 0 :=
  ccm17_smallShuffleFace_right_zero q s i (ccm17_shuffleRight s i)
    (ccm17_shuffle_consecutive_right_omit s i ha ha' hb hb')

#print axioms ccm17_smallShuffleFace_first_zero
#print axioms ccm17_smallShuffleFace_last_zero
#print axioms ccm17_smallShuffleFace_consecutive_left_zero
#print axioms ccm17_smallShuffleFace_consecutive_right_zero

private theorem ccm17_swapShuffle_first_forward {n : ℕ} (k : Fin (n + 1))
    (s : ccm17_Shuffle n) (ha : s.1.1 = k.castSucc) (hb : s.1.2 ≠ k.succ) :
    (ccm17_swapShuffle k s).1.1.val = s.1.1.val + 1 ∧
      (ccm17_swapShuffle k s).1.2 = s.1.2 := by
  have hab : k.castSucc < s.1.2 := ha ▸ s.2
  have hbk : s.1.2 ≠ k.castSucc := ne_of_gt hab
  have hlt : k.succ < s.1.2 := by
    have hb' : s.1.2.val ≠ k.val + 1 := fun h => hb (Fin.ext h)
    change k.val < s.1.2.val at hab
    change k.val + 1 < s.1.2.val
    omega
  simp only [ccm17_swapShuffle, ha, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hbk hb, dif_pos hlt, Fin.val_succ, Fin.val_castSucc]
  constructor <;> trivial

private theorem ccm17_swapShuffle_second_forward {n : ℕ} (k : Fin (n + 1))
    (s : ccm17_Shuffle n) (hb : s.1.2 = k.castSucc) :
    (ccm17_swapShuffle k s).1.1 = s.1.1 ∧
      (ccm17_swapShuffle k s).1.2.val = s.1.2.val + 1 := by
  have hab : s.1.1 < k.castSucc := hb ▸ s.2
  have hak : s.1.1 ≠ k.castSucc := ne_of_lt hab
  have hlt : s.1.1 < k.succ := by
    change s.1.1.val < k.val at hab
    change s.1.1.val < k.val + 1
    omega
  have hak' : s.1.1 ≠ k.succ := ne_of_lt hlt
  simp only [ccm17_swapShuffle, hb, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hak hak', dif_pos hlt, Fin.val_succ, Fin.val_castSucc]
  constructor <;> trivial

private theorem ccm17_swapShuffle_first_backward {n : ℕ} (k : Fin (n + 1))
    (s : ccm17_Shuffle n) (ha : s.1.1 = k.succ) :
    s.1.1.val = (ccm17_swapShuffle k s).1.1.val + 1 ∧
      s.1.2 = (ccm17_swapShuffle k s).1.2 := by
  have hab : k.succ < s.1.2 := ha ▸ s.2
  have hbk' : s.1.2 ≠ k.succ := ne_of_gt hab
  have hlt : k.castSucc < s.1.2 := by
    change k.val + 1 < s.1.2.val at hab
    change k.val < s.1.2.val
    omega
  have hbk : s.1.2 ≠ k.castSucc := ne_of_gt hlt
  simp only [ccm17_swapShuffle, ha, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne hbk hbk', dif_pos hlt, Fin.val_succ, Fin.val_castSucc]
  constructor <;> trivial

private theorem ccm17_swapShuffle_second_backward {n : ℕ} (k : Fin (n + 1))
    (s : ccm17_Shuffle n) (hb : s.1.2 = k.succ) (ha : s.1.1 ≠ k.castSucc) :
    s.1.1 = (ccm17_swapShuffle k s).1.1 ∧
      s.1.2.val = (ccm17_swapShuffle k s).1.2.val + 1 := by
  have hab : s.1.1 < k.succ := hb ▸ s.2
  have hak' : s.1.1 ≠ k.succ := ne_of_lt hab
  have hlt : s.1.1 < k.castSucc := by
    have ha' : s.1.1.val ≠ k.val := fun h => ha (Fin.ext h)
    change s.1.1.val < k.val + 1 at hab
    change s.1.1.val < k.val
    omega
  simp only [ccm17_swapShuffle, hb, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne ha hak', dif_pos hlt, Fin.val_succ, Fin.val_castSucc]
  constructor <;> trivial

private theorem ccm17_swapShuffle_fixed_disjoint {n : ℕ} (k : Fin (n + 1))
    (s : ccm17_Shuffle n) (ha : s.1.1 ≠ k.castSucc) (ha' : s.1.1 ≠ k.succ)
    (hb : s.1.2 ≠ k.castSucc) (hb' : s.1.2 ≠ k.succ) :
    ccm17_swapShuffle k s = s := by
  apply Subtype.ext
  simp only [ccm17_swapShuffle, Equiv.swap_apply_of_ne_of_ne ha ha',
    Equiv.swap_apply_of_ne_of_ne hb hb', dif_pos s.2]

private theorem ccm17_swapShuffle_fixed_both {n : ℕ} (k : Fin (n + 1))
    (s : ccm17_Shuffle n) (ha : s.1.1 = k.castSucc) (hb : s.1.2 = k.succ) :
    ccm17_swapShuffle k s = s := by
  have hnot : ¬k.succ < k.castSucc := by
    change ¬k.val + 1 < k.val
    omega
  apply Subtype.ext
  change (ccm17_swapShuffle k s).1 = (s.1.1, s.1.2)
  simp only [ccm17_swapShuffle, ha, hb, Equiv.swap_apply_left,
    Equiv.swap_apply_right, dif_neg hnot]

#print axioms ccm17_swapShuffle_first_forward
#print axioms ccm17_swapShuffle_second_forward
#print axioms ccm17_swapShuffle_first_backward
#print axioms ccm17_swapShuffle_second_backward
#print axioms ccm17_swapShuffle_fixed_disjoint
#print axioms ccm17_swapShuffle_fixed_both

private def ccm17_signedSmallShuffleFace (q : ℕ) (s : ccm17_Shuffle (q * 2))
    (i : Fin (2 + q * 2 + 1)) :=
  (-1 : ℚ) ^ (s.1.1.val + s.1.2.val - 1) • ccm17_smallShuffleFace q s i

/-- Adjacent step interchange pairs every interior face with its negative;
fixed shuffles have a face in one of the two complements. -/
private theorem ccm17_smallShuffleFace_swap_cancel (q : ℕ) (k : Fin (q * 2 + 1))
    (s : ccm17_Shuffle (q * 2)) (i : Fin (2 + q * 2 + 1))
    (hi : i.val = k.val + 1) :
    ccm17_signedSmallShuffleFace q s i +
      ccm17_signedSmallShuffleFace q (ccm17_swapShuffle k s) i = 0 := by
  unfold ccm17_signedSmallShuffleFace
  by_cases ha : s.1.1 = k.castSucc
  · by_cases hb : s.1.2 = k.succ
    · rw [ccm17_swapShuffle_fixed_both k s ha hb]
      have hz := ccm17_smallShuffleFace_consecutive_left_zero q s
        (by simp only [ha, hb, Fin.val_succ, Fin.val_castSucc]) i
        (by simpa only [hb, Fin.val_succ] using hi)
      rw [hz, smul_zero, add_zero]
    · obtain ⟨hta, htb⟩ := ccm17_swapShuffle_first_forward k s ha hb
      exact ccm17_smallShuffleFace_cancel_first q s _ hta htb i
        (by simpa only [ha, Fin.val_castSucc] using hi)
  by_cases hb : s.1.2 = k.castSucc
  · obtain ⟨hta, htb⟩ := ccm17_swapShuffle_second_forward k s hb
    exact ccm17_smallShuffleFace_cancel_second q s _ hta htb i
      (by simpa only [hb, Fin.val_castSucc] using hi)
  by_cases ha' : s.1.1 = k.succ
  · obtain ⟨hta, htb⟩ := ccm17_swapShuffle_first_backward k s ha'
    have his : i.val = s.1.1.val := by simpa only [ha', Fin.val_succ] using hi
    exact (add_comm _ _).trans
      (ccm17_smallShuffleFace_cancel_first q _ s hta htb i (his.trans hta))
  by_cases hb' : s.1.2 = k.succ
  · obtain ⟨hta, htb⟩ := ccm17_swapShuffle_second_backward k s hb' ha
    have his : i.val = s.1.2.val := by simpa only [hb', Fin.val_succ] using hi
    exact (add_comm _ _).trans
      (ccm17_smallShuffleFace_cancel_second q _ s hta htb i (his.trans htb))
  rw [ccm17_swapShuffle_fixed_disjoint k s ha ha' hb hb']
  have hav : s.1.1.val ≠ k.val := fun h => ha (Fin.ext h)
  have hav' : s.1.1.val ≠ k.val + 1 := fun h => ha' (Fin.ext h)
  have hbv : s.1.2.val ≠ k.val := fun h => hb (Fin.ext h)
  have hbv' : s.1.2.val ≠ k.val + 1 := fun h => hb' (Fin.ext h)
  rw [ccm17_smallShuffleFace_consecutive_right_zero q s i
    (by omega) (by omega) (by omega) (by omega), smul_zero, add_zero]

/-- The signed sum of the projected shuffle faces at every interior vertex
vanishes by the adjacent-step involution. -/
private theorem ccm17_smallShuffleFace_sum_interior (q : ℕ)
    (k : Fin (q * 2 + 1)) (i : Fin (2 + q * 2 + 1)) (hi : i.val = k.val + 1) :
    ∑ s : ccm17_Shuffle (q * 2), ccm17_signedSmallShuffleFace q s i = 0 := by
  classical
  apply Finset.sum_ninvolution (ccm17_swapShuffle k)
  · intro s
    exact ccm17_smallShuffleFace_swap_cancel q k s i hi
  · intro s hs he
    have h := ccm17_smallShuffleFace_swap_cancel q k s i hi
    rw [he] at h
    have hz : (2 : ℚ) • ccm17_signedSmallShuffleFace q s i = 0 := by
      simpa only [two_smul] using h
    exact hs ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  · intro s
    exact Finset.mem_univ _
  · exact ccm17_swapShuffle_involutive k

#print axioms ccm17_smallShuffleFace_swap_cancel
#print axioms ccm17_smallShuffleFace_sum_interior

/-- The signed shuffle-face sum is zero at every vertex, including both endpoints. -/
private theorem ccm17_smallShuffleFace_sum (q : ℕ) (i : Fin (2 + q * 2 + 1)) :
    ∑ s : ccm17_Shuffle (q * 2), ccm17_signedSmallShuffleFace q s i = 0 := by
  classical
  by_cases hi0 : i = 0
  · subst i
    apply Finset.sum_eq_zero
    intro s _
    simp only [ccm17_signedSmallShuffleFace, ccm17_smallShuffleFace_first_zero, smul_zero]
  by_cases hil : i = Fin.last (2 + q * 2)
  · subst i
    apply Finset.sum_eq_zero
    intro s _
    simp only [ccm17_signedSmallShuffleFace, ccm17_smallShuffleFace_last_zero, smul_zero]
  have hv0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
  have hvl : i.val ≠ 2 + q * 2 := fun h => hil (Fin.ext h)
  let k : Fin (q * 2 + 1) := ⟨i.val - 1, by omega⟩
  exact ccm17_smallShuffleFace_sum_interior q k i (by dsimp [k]; omega)

/-- The full alternating boundary-face sum vanishes in the small relative
complex, with the shuffle sign and the simplicial boundary sign both retained. -/
private theorem ccm17_smallShuffleFace_boundary_sum (q : ℕ) :
    ∑ s : ccm17_Shuffle (q * 2), ∑ i : Fin (2 + q * 2 + 1),
      (-1 : ℚ) ^ i.val • ccm17_signedSmallShuffleFace q s i = 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.smul_sum, ccm17_smallShuffleFace_sum, smul_zero]

#print axioms ccm17_smallShuffleFace_sum
#print axioms ccm17_smallShuffleFace_boundary_sum

open scoped Simplicial in
/-- The differential of an affine product simplex, with the source degree
written independently of the predecessor degree. -/
private theorem ccm17_complexProductSimplex_boundary (q n m : ℕ) (h : n = m + 1)
    (a : Fin (n + 1) → Fin 3) (b : Fin (n + 1) → Fin (q * 2 + 1)) :
    (((TopCat.toSSet.obj (TopCat.of (Fin (q + 1) → ℂ))).chainComplex
      (ModuleCat.of ℚ ℚ)).d n m).hom
      (chainOfSimplex ℚ (ccm17_complexProductSimplex q a b)) =
    ∑ i : Fin (n + 1), (-1 : ℚ) ^ i.val • chainOfSimplex ℚ
      (ccm17_complexProductSimplex q
        (fun j : Fin (m + 1) => a (i.succAbove ⟨j.val, by omega⟩))
        (fun j : Fin (m + 1) => b (i.succAbove ⟨j.val, by omega⟩))) := by
  subst n
  change boundary ℚ m _ = _
  rw [boundary_chainOfSimplex]
  apply Finset.sum_congr rfl
  intro i _
  rw [ccm17_complexProductSimplex_face]
  rfl

#print axioms ccm17_complexProductSimplex_boundary

/-- The transported shuffle chain is the signed sum of the complex affine
product simplices. -/
private theorem ccm17_complexShuffleChain_eq_sum (q : ℕ) :
    ccm17_complexShuffleChain q =
      ∑ s : ccm17_Shuffle (q * 2),
        (-1 : ℚ) ^ (s.1.1.val + s.1.2.val - 1) •
          chainOfSimplex ℚ (ccm17_complexProductSimplex q
            (ccm17_shuffleLeft s) (ccm17_shuffleRight s)) := by
  unfold ccm17_complexShuffleChain ccm17_shuffleChain
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_smul, chainOfSimplex_map]
  rfl

#print axioms ccm17_complexShuffleChain_eq_sum

/-- The signed shuffle chain has zero differential after projection to the
small relative complex. -/
private theorem ccm17_complexShuffleChain_small_boundary (q : ℕ) :
    ((ccm14_smallRelativeComplex (TopCat.of (Fin (q + 1) → ℂ))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q))).d
        (2 + q * 2) (q * 2 + 1)).hom
      (((ccm14_smallProjection (TopCat.of (Fin (q + 1) → ℂ))
        (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
        (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q))).f
          (2 + q * 2)).hom (ccm17_complexShuffleChain q)) = 0 := by
  let Y := TopCat.of (Fin (q + 1) → ℂ)
  let S := ccm17_zeroSupport Y 1 (ccm17_head q)
  let T := ccm17_zeroSupport Y q (ccm17_tail q)
  have hcomm := ConcreteCategory.congr_hom
    ((ccm14_smallProjection Y S T).comm (2 + q * 2) (q * 2 + 1))
    (ccm17_complexShuffleChain q)
  rw [show ((ccm14_smallRelativeComplex Y S T).d (2 + q * 2) (q * 2 + 1)).hom
      (((ccm14_smallProjection Y S T).f (2 + q * 2)).hom
        (ccm17_complexShuffleChain q)) =
      ((ccm14_smallProjection Y S T).f (q * 2 + 1)).hom
        ((((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).d
          (2 + q * 2) (q * 2 + 1)).hom (ccm17_complexShuffleChain q)) from hcomm]
  rw [ccm17_complexShuffleChain_eq_sum]
  simp only [map_sum, map_smul]
  convert ccm17_smallShuffleFace_boundary_sum q using 1
  apply Finset.sum_congr rfl
  intro s _
  rw [ccm17_complexProductSimplex_boundary q _ _ (by omega)]
  simp only [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

#print axioms ccm17_complexShuffleChain_small_boundary

/-- The explicit projected shuffle chain as a cycle of the small relative
complex, retaining its actual chain representative. -/
private def ccm17_smallShuffleCycle (q : ℕ) :
    LinearMap.ker ((ccm14_smallRelativeComplex (TopCat.of (Fin (q + 1) → ℂ))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q))).sc
        (2 + q * 2)).g.hom :=
  ⟨((ccm14_smallProjection (TopCat.of (Fin (q + 1) → ℂ))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q))).f
        (2 + q * 2)).hom (ccm17_complexShuffleChain q), by
    have hnext : (ComplexShape.down ℕ).next (2 + q * 2) = q * 2 + 1 :=
      (ComplexShape.down ℕ).next_eq' (by change q * 2 + 1 + 1 = 2 + q * 2; omega)
    change ((ccm14_smallRelativeComplex _ _ _).d (2 + q * 2)
      ((ComplexShape.down ℕ).next (2 + q * 2))).hom _ = 0
    rw [hnext]
    exact ccm17_complexShuffleChain_small_boundary q⟩

#print axioms ccm17_smallShuffleCycle

/-- A categorical dual cocycle has an explicit kernel representative with
the same cochain and the same cohomology class. -/
private theorem ccm17_dualCycle_representative
    (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (c : K.linearDualCochainComplex.cycles n) :
    ∃ a : LinearMap.ker (K.sc n).linearDual.g.hom,
      ccm17_dualClass K n a = K.linearDualCochainComplex.homologyπ n c ∧
      a.1 = K.linearDualCochainComplex.iCycles n c := by
  let T := (K.sc n).linearDual
  let e := HomologicalComplex.linearDualCochainComplexScIso K n
  let w := ShortComplex.cyclesMap e.hom c
  let a := T.moduleCatCyclesIso.hom w
  refine ⟨a, ?_, ?_⟩
  · apply (ccm17_dualEquiv K n).symm.injective
    simp only [ccm17_dualClass, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply]
    change T.moduleCatHomologyClass a =
      ShortComplex.homologyMap e.hom (K.linearDualCochainComplex.homologyπ n c)
    have hπ := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality e.hom) c
    change ShortComplex.homologyMap e.hom
      (K.linearDualCochainComplex.homologyπ n c) = T.homologyπ w at hπ
    rw [hπ]
    have h := ConcreteCategory.congr_hom T.moduleCatCyclesIso_inv_π a
    change T.homologyπ (T.moduleCatCyclesIso.inv a) = T.moduleCatHomologyClass a at h
    rw [show T.moduleCatCyclesIso.inv a = w from
      ConcreteCategory.congr_hom T.moduleCatCyclesIso.hom_inv_id w] at h
    exact h.symm
  · have h := ConcreteCategory.congr_hom T.moduleCatCyclesIso_hom_i w
    change a.1 = T.iCycles w at h
    rw [h]
    change (ShortComplex.cyclesMap e.hom ≫ T.iCycles) c = _
    rw [ShortComplex.cyclesMap_i]
    rfl

#print axioms ccm17_dualCycle_representative

/-- The comparison image of the explicit shuffle cycle in relative homology. -/
private def ccm17_shuffleHomologyClass (q : ℕ) :
    RelativeHomology ℚ
      (TopPair.ofSubset (X := TopCat.of (Fin (q + 1) → ℂ))
        ((ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q) ⊓
          ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q) :
            Closeds (Fin (q + 1) → ℂ)) : Set (Fin (q + 1) → ℂ))ᶜ) (2 + q * 2) :=
  HomologicalComplex.homologyMap
    (ccm14_relativeComparison (TopCat.of (Fin (q + 1) → ℂ))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q))) (2 + q * 2)
    (((ccm14_smallRelativeComplex (TopCat.of (Fin (q + 1) → ℂ))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q))).sc
        (2 + q * 2)).moduleCatHomologyClass (ccm17_smallShuffleCycle q))

#print axioms ccm17_shuffleHomologyClass

/-- The normalized product coclass evaluates to one on the comparison
class of the shuffle cycle. -/
private theorem ccm17_shuffleHomologyClass_evaluation (q : ℕ) :
    let Y := TopCat.of (Fin (q + 1) → ℂ)
    let S := ccm17_zeroSupport Y 1 (ccm17_head q)
    let T := ccm17_zeroSupport Y q (ccm17_tail q)
    relativeCohomologyEquivDualHomology ℚ
      (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ) (2 + q * 2)
      (ccm15_relativeCup Y S T 2 (q * 2)
        (ccm17_normalClass Y 1 (ccm17_head q))
        (relativeCohomologyMap ℚ (q * 2) (ccm17_normalPair Y q (ccm17_tail q))
          ((Nat.mul_comm q 2).symm ▸ normalizedPointCoclass q)))
      (ccm17_shuffleHomologyClass q) = 1 := by
  dsimp only
  let Y := TopCat.of (Fin (q + 1) → ℂ)
  let S := ccm17_zeroSupport Y 1 (ccm17_head q)
  let T := ccm17_zeroSupport Y q (ccm17_tail q)
  obtain ⟨u, v, hu, hv, he⟩ := ccm17_normalized_complexShuffle_evaluation q
  obtain ⟨a, ha, ha'⟩ := ccm17_dualCycle_representative
    ((relativeChainFunctor ℚ).obj (puncturedPair ℂ 1)) 2 u
  obtain ⟨b, hb, hb'⟩ := ccm17_dualCycle_representative
    ((relativeChainFunctor ℚ).obj (puncturedPair ℂ q)) (q * 2) v
  unfold ccm17_normalClass
  rw [← hu, ← hv, ← ha, ← hb]
  change relativeCohomologyEquivDualHomology ℚ _ (2 + q * 2)
    (ccm15_relativeCup Y S T 2 (q * 2)
      (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap
        ((relativeChainFunctor ℚ).map (ccm17_normalPair Y 1 (ccm17_head q)))) 2
        (ccm17_dualClass _ 2 a))
      (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap
        ((relativeChainFunctor ℚ).map (ccm17_normalPair Y q (ccm17_tail q)))) (q * 2)
        (ccm17_dualClass _ (q * 2) b))) _ = 1
  rw [ccm17_dualClass_naturality, ccm17_dualClass_naturality]
  unfold ccm17_shuffleHomologyClass
  erw [ccm17_relativeCup_evaluation_lift Y S T 2 (q * 2) _ _
    (ccm17_smallShuffleCycle q) (ccm17_complexShuffleChain q) rfl]
  change ccm13_relativeCupLift Y S T 2 (q * 2)
    ((relativeCochainComplexMap ℚ (ccm17_normalPair Y 1 (ccm17_head q))).f 2 a.1)
    ((relativeCochainComplexMap ℚ (ccm17_normalPair Y q (ccm17_tail q))).f (q * 2) b.1)
    (ccm17_complexShuffleChain q) = 1
  rw [ha', hb']
  exact he

#print axioms ccm17_shuffleHomologyClass_evaluation

/-- Degree transport commutes with a relative pullback, cup product, and
evaluation against a homology class. -/
private theorem ccm17_relativeCup_pairing_degree_cast
    (Y : TopCat.{0}) (S T : Closeds Y) (p : ℕ) {P : TopPair.{0}}
    (f : TopPair.ofSubset (T : Set Y)ᶜ ⟶ P) {m n : ℕ} (h : m = n)
    (u : RelativeCohomology ℚ (TopPair.ofSubset (S : Set Y)ᶜ) p)
    (v : RelativeCohomology ℚ P n)
    (z : RelativeHomology ℚ (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ) (p + m)) :
    relativeCohomologyEquivDualHomology ℚ _ (p + m)
      (ccm15_relativeCup Y S T p m u (relativeCohomologyMap ℚ m f (h.symm ▸ v))) z =
    relativeCohomologyEquivDualHomology ℚ _ (p + n)
      (ccm15_relativeCup Y S T p n u (relativeCohomologyMap ℚ n f v))
      ((congrArg (p + ·) h) ▸ z) := by
  subst n
  rfl

#print axioms ccm17_relativeCup_pairing_degree_cast

/-- The cup product appearing in the frozen coordinate statement evaluates
to one on the shuffle homology class in degree two plus twice q. -/
private theorem ccm17_shuffleHomologyClass_evaluation_cast (q : ℕ) :
    let Y := TopCat.of (Fin (q + 1) → ℂ)
    let S := ccm17_zeroSupport Y 1 (ccm17_head q)
    let T := ccm17_zeroSupport Y q (ccm17_tail q)
    relativeCohomologyEquivDualHomology ℚ
      (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ) (2 + 2 * q)
      (ccm15_relativeCup Y S T 2 (2 * q)
        (ccm17_normalClass Y 1 (ccm17_head q))
        (ccm17_normalClass Y q (ccm17_tail q)))
      ((congrArg (2 + ·) (Nat.mul_comm q 2)) ▸ ccm17_shuffleHomologyClass q) = 1 := by
  let Y := TopCat.of (Fin (q + 1) → ℂ)
  let S := ccm17_zeroSupport Y 1 (ccm17_head q)
  let T := ccm17_zeroSupport Y q (ccm17_tail q)
  have h := ccm17_relativeCup_pairing_degree_cast Y S T 2
    (ccm17_normalPair Y q (ccm17_tail q)) (Nat.mul_comm q 2)
    (ccm17_normalClass Y 1 (ccm17_head q)) (normalizedPointCoclass q)
    (ccm17_shuffleHomologyClass q)
  exact h.symm.trans (ccm17_shuffleHomologyClass_evaluation q)

#print axioms ccm17_shuffleHomologyClass_evaluation_cast

/-- Both the shuffle homology class and the normalized coordinate cup product
are nonzero, as witnessed by their unit pairing. -/
private theorem ccm17_shuffleHomologyClass_and_coordinateCup_ne_zero (q : ℕ) :
    ccm17_shuffleHomologyClass q ≠ 0 ∧
      ccm15_relativeCup (TopCat.of (Fin (q + 1) → ℂ))
        (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
        (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q)) 2 (2 * q)
        (ccm17_normalClass (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
        (ccm17_normalClass (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q)) ≠ 0 := by
  constructor
  · intro hz
    have h := ccm17_shuffleHomologyClass_evaluation q
    dsimp only at h
    rw [hz, map_zero] at h
    exact zero_ne_one h
  · intro hz
    have h := ccm17_shuffleHomologyClass_evaluation_cast q
    dsimp only at h
    rw [hz, map_zero, LinearMap.zero_apply] at h
    exact zero_ne_one h

#print axioms ccm17_shuffleHomologyClass_and_coordinateCup_ne_zero

/-- The relative class of an explicit chain whose boundary vanishes in relative chains. -/
private def ccm17_chainClass (P : TopPair.{0}) (n : ℕ)
    (c : ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).X n)
    (hc : (((relativeChainFunctor ℚ).obj P).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ P).f n).hom c) = 0) :
    RelativeHomology ℚ P n :=
  (((relativeChainFunctor ℚ).obj P).sc n).moduleCatHomologyClass ⟨_, hc⟩

private theorem ccm17_chainClass_congr (P : TopPair.{0}) (n : ℕ)
    (c c' : ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).X n)
    (hc : (((relativeChainFunctor ℚ).obj P).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ P).f n).hom c) = 0)
    (hc' : (((relativeChainFunctor ℚ).obj P).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ P).f n).hom c') = 0)
    (h : ((relativeChainProjection ℚ P).f n).hom c =
      ((relativeChainProjection ℚ P).f n).hom c') :
    ccm17_chainClass P n c hc = ccm17_chainClass P n c' hc' := by
  unfold ccm17_chainClass
  congr 1
  exact Subtype.ext h

private theorem ccm17_chainClass_map {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ)
    (c : ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).X n)
    (hc : (((relativeChainFunctor ℚ).obj P).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ P).f n).hom c) = 0)
    (hc' : (((relativeChainFunctor ℚ).obj Q).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ Q).f n).hom
        (((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f))
          (ModuleCat.of ℚ ℚ)).f n).hom c)) = 0) :
    relativeHomologyMap ℚ n f (ccm17_chainClass P n c hc) =
      ccm17_chainClass Q n (((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f))
          (ModuleCat.of ℚ ℚ)).f n).hom c) hc' := by
  unfold ccm17_chainClass
  refine (ShortComplex.moduleCatHomologyClass_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) n).map
      ((relativeChainFunctor ℚ).map f)) _).trans ?_
  congr 1
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (congrArg (fun g => g.f n)
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)) c


private theorem ccm17_chainClass_eq_homologyπ (P : TopPair.{0}) (n : ℕ)
    (c : ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of ℚ ℚ)).X n)
    (hc : (((relativeChainFunctor ℚ).obj P).d n ((ComplexShape.down ℕ).next n)).hom
      (((relativeChainProjection ℚ P).f n).hom c) = 0)
    (z : ((relativeChainFunctor ℚ).obj P).cycles n)
    (hz : (((relativeChainFunctor ℚ).obj P).iCycles n).hom z =
      ((relativeChainProjection ℚ P).f n).hom c) :
    ccm17_chainClass P n c hc = (((relativeChainFunctor ℚ).obj P).homologyπ n).hom z := by
  let S := ((relativeChainFunctor ℚ).obj P).sc n
  have h1 : ccm17_chainClass P n c hc =
      (S.moduleCatCyclesIso.inv ≫ S.homologyπ).hom ⟨_, hc⟩ := by
    rw [ShortComplex.moduleCatCyclesIso_inv_π]
    rfl
  rw [h1]
  change S.homologyπ.hom (S.moduleCatCyclesIso.inv.hom ⟨_, hc⟩) = S.homologyπ.hom z
  congr 1
  apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles_apply]
  exact hz.symm

private theorem ccm17_standardLocalClass_eq_chainClass (d : ℕ)
    (hc : (((relativeChainFunctor ℚ).obj (puncturedPair ℝ d)).d d
      ((ComplexShape.down ℕ).next d)).hom
      (((relativeChainProjection ℚ (puncturedPair ℝ d)).f d).hom
        (chainOfSimplex ℚ (standardSingularSimplex d))) = 0) :
    standardLocalClass ℚ d =
      ccm17_chainClass (puncturedPair ℝ d) d
        (chainOfSimplex ℚ (standardSingularSimplex d)) hc := by
  rw [ccm17_chainClass_eq_homologyπ _ _ _ _ ((standardLocalCycle ℚ d).hom 1)]
  · rfl
  · change ((standardLocalCycle ℚ d ≫
      (standardLocalRelativeChainComplex ℚ d).iCycles d).hom) 1 = _
    rw [standardLocalCycle, HomologicalComplex.liftCycles_i]
    rfl

/-- A homotopy of maps of subset pairs from one continuous family. -/
private def ccm17_ofSubsetHomotopy {X Y : TopCat.{0}} {A : Set X} {B : Set Y}
    (F : C(unitInterval × X, Y)) (hF : ∀ s, ∀ a ∈ A, F (s, a) ∈ B) :
    TopPair.Homotopy
      (TopPair.ofSubsetHom (TopCat.ofHom ⟨fun x => F (0, x), by fun_prop⟩)
        (fun a ha => hF 0 a ha))
      (TopPair.ofSubsetHom (TopCat.ofHom ⟨fun x => F (1, x), by fun_prop⟩)
        (fun a ha => hF 1 a ha)) where
  fst :=
    { toFun := F
      continuous_toFun := F.continuous
      map_zero_left := fun _ => rfl
      map_one_left := fun _ => rfl }
  snd :=
    { toFun := fun p => ⟨F (p.1, p.2.1), hF p.1 p.2.1 p.2.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact F.continuous.comp (continuous_fst.prodMk
          (continuous_subtype_val.comp continuous_snd))
      map_zero_left := fun _ => rfl
      map_one_left := fun _ => rfl }
  w := rfl

section GenericFaces

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℚ M]

/-- A signed face of a shuffle simplex, read through an arbitrary function of
its two vertex maps. -/
private def ccm17_signedFace
    (F : (Fin (2 + n) → Fin 3) → (Fin (2 + n) → Fin (n + 1)) → M)
    (s : ccm17_Shuffle n) (i : Fin (2 + n + 1)) : M :=
  (-1 : ℚ) ^ (s.1.1.val + s.1.2.val - 1) •
    F (fun j => ccm17_shuffleLeft s (i.succAbove j))
      (fun j => ccm17_shuffleRight s (i.succAbove j))

private theorem ccm17_signedFace_swap_cancel
    (F : (Fin (2 + n) → Fin 3) → (Fin (2 + n) → Fin (n + 1)) → M)
    (hL : ∀ a b (j : Fin 3), (∀ i, a i ≠ j) → F a b = 0)
    (hR : ∀ a b (j : Fin (n + 1)), (∀ i, b i ≠ j) → F a b = 0)
    (k : Fin (n + 1)) (s : ccm17_Shuffle n) (i : Fin (2 + n + 1))
    (hi : i.val = k.val + 1) :
    ccm17_signedFace F s i + ccm17_signedFace F (ccm17_swapShuffle k s) i = 0 := by
  have cancel_first : ∀ (s t : ccm17_Shuffle n), t.1.1.val = s.1.1.val + 1 →
      t.1.2 = s.1.2 → i.val = s.1.1.val + 1 →
      ccm17_signedFace F s i + ccm17_signedFace F t i = 0 := by
    intro s t ha hb hi
    obtain ⟨hl, hr⟩ := ccm17_shuffle_move_first_face s t ha hb i hi
    unfold ccm17_signedFace
    rw [hl, hr, ccm17_shuffle_sign_slide s t (by rw [ha, hb]; omega)]
    simp only [neg_smul, add_neg_cancel]
  have cancel_second : ∀ (s t : ccm17_Shuffle n), t.1.1 = s.1.1 →
      t.1.2.val = s.1.2.val + 1 → i.val = s.1.2.val + 1 →
      ccm17_signedFace F s i + ccm17_signedFace F t i = 0 := by
    intro s t ha hb hi
    obtain ⟨hl, hr⟩ := ccm17_shuffle_move_second_face s t ha hb i hi
    unfold ccm17_signedFace
    rw [hl, hr, ccm17_shuffle_sign_slide s t (by rw [ha, hb]; omega)]
    simp only [neg_smul, add_neg_cancel]
  by_cases ha : s.1.1 = k.castSucc
  · by_cases hb : s.1.2 = k.succ
    · rw [ccm17_swapShuffle_fixed_both k s ha hb]
      have hz : ccm17_signedFace F s i = 0 := by
        unfold ccm17_signedFace
        rw [hL _ _ 1 (ccm17_shuffle_consecutive_left_omit s
          (by simp only [ha, hb, Fin.val_succ, Fin.val_castSucc]) i
          (by simpa only [hb, Fin.val_succ] using hi)), smul_zero]
      rw [hz, add_zero]
    · obtain ⟨hta, htb⟩ := ccm17_swapShuffle_first_forward k s ha hb
      exact cancel_first s _ hta htb (by simpa only [ha, Fin.val_castSucc] using hi)
  by_cases hb : s.1.2 = k.castSucc
  · obtain ⟨hta, htb⟩ := ccm17_swapShuffle_second_forward k s hb
    exact cancel_second s _ hta htb (by simpa only [hb, Fin.val_castSucc] using hi)
  by_cases ha' : s.1.1 = k.succ
  · obtain ⟨hta, htb⟩ := ccm17_swapShuffle_first_backward k s ha'
    have his : i.val = s.1.1.val := by simpa only [ha', Fin.val_succ] using hi
    exact (add_comm _ _).trans (cancel_first _ s hta htb (his.trans hta))
  by_cases hb' : s.1.2 = k.succ
  · obtain ⟨hta, htb⟩ := ccm17_swapShuffle_second_backward k s hb' ha
    have his : i.val = s.1.2.val := by simpa only [hb', Fin.val_succ] using hi
    exact (add_comm _ _).trans (cancel_second _ s hta htb (his.trans htb))
  rw [ccm17_swapShuffle_fixed_disjoint k s ha ha' hb hb']
  have hav : s.1.1.val ≠ k.val := fun h => ha (Fin.ext h)
  have hav' : s.1.1.val ≠ k.val + 1 := fun h => ha' (Fin.ext h)
  have hbv : s.1.2.val ≠ k.val := fun h => hb (Fin.ext h)
  have hbv' : s.1.2.val ≠ k.val + 1 := fun h => hb' (Fin.ext h)
  have hz : ccm17_signedFace F s i = 0 := by
    unfold ccm17_signedFace
    rw [hR _ _ (ccm17_shuffleRight s i) (ccm17_shuffle_consecutive_right_omit s i
      (by omega) (by omega) (by omega) (by omega)), smul_zero]
  rw [hz, add_zero]

/-- The alternating sum of all shuffle faces vanishes for any face function that
kills vertex maps omitting a vertex of either factor. -/
private theorem ccm17_signedFace_boundary_sum
    (F : (Fin (2 + n) → Fin 3) → (Fin (2 + n) → Fin (n + 1)) → M)
    (hL : ∀ a b (j : Fin 3), (∀ i, a i ≠ j) → F a b = 0)
    (hR : ∀ a b (j : Fin (n + 1)), (∀ i, b i ≠ j) → F a b = 0) :
    ∑ s : ccm17_Shuffle n, ∑ i : Fin (2 + n + 1),
      (-1 : ℚ) ^ i.val • ccm17_signedFace F s i = 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.smul_sum]
  convert smul_zero ((-1 : ℚ) ^ i.val)
  by_cases hi0 : i = 0
  · subst i
    apply Finset.sum_eq_zero
    intro s _
    unfold ccm17_signedFace
    by_cases hs : s.1.1.val = 0
    · rw [hL _ _ 0 (fun j => by
        simpa only [Fin.zero_succAbove] using ccm17_shuffle_first_left_omit s hs j),
        smul_zero]
    · rw [hR _ _ 0 (fun j => by
        simpa only [Fin.zero_succAbove] using ccm17_shuffle_first_right_omit s hs j),
        smul_zero]
  by_cases hil : i = Fin.last (2 + n)
  · subst i
    apply Finset.sum_eq_zero
    intro s _
    unfold ccm17_signedFace
    by_cases hs : s.1.2.val = n + 1
    · rw [hL _ _ (Fin.last 2) (fun j => by
        simpa only [Fin.succAbove_last] using ccm17_shuffle_last_left_omit s hs j),
        smul_zero]
    · rw [hR _ _ (Fin.last n) (fun j => by
        simpa only [Fin.succAbove_last] using ccm17_shuffle_last_right_omit s hs j),
        smul_zero]
  have hv0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
  have hvl : i.val ≠ 2 + n := fun h => hil (Fin.ext h)
  let k : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hi : i.val = k.val + 1 := by dsimp [k]; omega
  apply Finset.sum_ninvolution (ccm17_swapShuffle k)
  · intro s
    exact ccm17_signedFace_swap_cancel F hL hR k s i hi
  · intro s hs he
    have h := ccm17_signedFace_swap_cancel F hL hR k s i hi
    rw [he] at h
    have hz : (2 : ℚ) • ccm17_signedFace F s i = 0 := by
      simpa only [two_smul] using h
    exact hs ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  · intro s
    exact Finset.mem_univ _
  · exact ccm17_swapShuffle_involutive k

end GenericFaces


open scoped Simplicial in
open Convexity in
/-- A product affine simplex in real block coordinates, translated by a vector. -/
private def ccm17_realProductSimplex (n : ℕ) {m : ℕ}
    (a : Fin (m + 1) → Fin 3) (b : Fin (m + 1) → Fin (n + 1)) (v : Fin (2 + n) → ℝ) :
    (TopCat.toSSet.obj (TopCat.of (Fin (2 + n) → ℝ))) _⦋m⦌ :=
  ((TopCat.of (Fin (2 + n) → ℝ)).toSSetObjEquiv _).symm
    ⟨fun t => Fin.append (standardAffineSimplex 2 (StdSimplex.map a t))
      (standardAffineSimplex n (StdSimplex.map b t)) + v, by
        apply Continuous.add _ continuous_const
        apply continuous_pi
        intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp only [Fin.append_left]
          fun_prop
        · simp only [Fin.append_right]
          fun_prop⟩

open scoped Simplicial in
private theorem ccm17_realProductSimplex_face (n m : ℕ)
    (a : Fin (m + 2) → Fin 3) (b : Fin (m + 2) → Fin (n + 1)) (v : Fin (2 + n) → ℝ)
    (i : Fin (m + 2)) :
    (TopCat.toSSet.obj (TopCat.of (Fin (2 + n) → ℝ))).δ i
      (ccm17_realProductSimplex n a b v) =
    ccm17_realProductSimplex n (a ∘ i.succAbove) (b ∘ i.succAbove) v := by
  apply ((TopCat.of (Fin (2 + n) → ℝ)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  change Fin.append
    (standardAffineSimplex 2 (Convexity.StdSimplex.map a (Convexity.StdSimplex.map _ t)))
    (standardAffineSimplex n (Convexity.StdSimplex.map b (Convexity.StdSimplex.map _ t))) + v = _
  rw [← Convexity.StdSimplex.map_comp, ← Convexity.StdSimplex.map_comp]
  rfl

open scoped Simplicial in
/-- A simplex with range in the subspace vanishes in relative chains. -/
private theorem ccm17_relativeProjection_simplex_zero (X : TopCat.{0}) (B : Set X)
    {m : ℕ} (σ : (TopCat.toSSet.obj X) _⦋m⦌)
    (hσ : ∀ t, X.toSSetObjEquiv _ σ t ∈ B) :
    ((relativeChainProjection ℚ (TopPair.ofSubset B)).f m).hom (chainOfSimplex ℚ σ) = 0 := by
  let P := TopPair.ofSubset B
  let τ := (P.snd.toSSetObjEquiv (.op (SimplexCategory.mk m))).symm
    ⟨fun t => ⟨X.toSSetObjEquiv _ σ t, hσ t⟩, by fun_prop⟩
  have hτ : (TopCat.toSSet.map P.map).app _ τ = σ := by
    apply (X.toSSetObjEquiv _).injective
    rfl
  have h := ConcreteCategory.congr_hom
    (iota_subspace_relativeChainProjection ℚ P τ) 1
  rw [hτ] at h
  exact h


/-- The signed shuffle chain in real block coordinates, translated by a vector. -/
private def ccm17_realShuffleChain (n : ℕ) (v : Fin (2 + n) → ℝ) :
    ((TopCat.toSSet.obj (TopCat.of (Fin (2 + n) → ℝ))).chainComplex
      (ModuleCat.of ℚ ℚ)).X (2 + n) :=
  ∑ s : ccm17_Shuffle n, (-1 : ℚ) ^ (s.1.1.val + s.1.2.val - 1) •
    chainOfSimplex ℚ (ccm17_realProductSimplex n (ccm17_shuffleLeft s)
      (ccm17_shuffleRight s) v)

open scoped Simplicial in
private theorem ccm17_realProductSimplex_boundary (n k m : ℕ) (h : k = m + 1)
    (a : Fin (k + 1) → Fin 3) (b : Fin (k + 1) → Fin (n + 1)) (v : Fin (2 + n) → ℝ) :
    (((TopCat.toSSet.obj (TopCat.of (Fin (2 + n) → ℝ))).chainComplex
      (ModuleCat.of ℚ ℚ)).d k m).hom
      (chainOfSimplex ℚ (ccm17_realProductSimplex n a b v)) =
    ∑ i : Fin (k + 1), (-1 : ℚ) ^ i.val • chainOfSimplex ℚ
      (ccm17_realProductSimplex n
        (fun j : Fin (m + 1) => a (i.succAbove ⟨j.val, by omega⟩))
        (fun j : Fin (m + 1) => b (i.succAbove ⟨j.val, by omega⟩)) v) := by
  subst k
  change boundary ℚ m _ = _
  rw [boundary_chainOfSimplex]
  apply Finset.sum_congr rfl
  intro i _
  rw [ccm17_realProductSimplex_face]
  rfl

/-- The real shuffle chain is a relative cycle for any subspace containing every
product face that omits a vertex of either factor. -/
private theorem ccm17_realShuffleChain_cycle (n : ℕ) (v : Fin (2 + n) → ℝ)
    (B : Set (Fin (2 + n) → ℝ))
    (hL : ∀ (a : Fin (n + 1 + 1) → Fin 3) (b : Fin (n + 1 + 1) → Fin (n + 1)) (j : Fin 3),
      (∀ i, a i ≠ j) → ∀ t, (TopCat.of (Fin (2 + n) → ℝ)).toSSetObjEquiv _
        (ccm17_realProductSimplex n a b v) t ∈ B)
    (hR : ∀ (a : Fin (n + 1 + 1) → Fin 3) (b : Fin (n + 1 + 1) → Fin (n + 1))
      (j : Fin (n + 1)), (∀ i, b i ≠ j) → ∀ t, (TopCat.of (Fin (2 + n) → ℝ)).toSSetObjEquiv _
        (ccm17_realProductSimplex n a b v) t ∈ B) :
    (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of (Fin (2 + n) → ℝ)) B)).d (2 + n)
      ((ComplexShape.down ℕ).next (2 + n))).hom
      (((relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of (Fin (2 + n) → ℝ)) B)).f (2 + n)).hom
        (ccm17_realShuffleChain n v)) = 0 := by
  let X := TopCat.of (Fin (2 + n) → ℝ)
  let π := relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of (Fin (2 + n) → ℝ)) B)
  have hnext : (ComplexShape.down ℕ).next (2 + n) = n + 1 :=
    (ComplexShape.down ℕ).next_eq' (by change n + 1 + 1 = 2 + n; omega)
  rw [hnext]
  have hcomm := ConcreteCategory.congr_hom (π.comm (2 + n) (n + 1))
    (ccm17_realShuffleChain n v)
  change (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of (Fin (2 + n) → ℝ)) B)).d (2 + n) (n + 1)).hom
    ((π.f (2 + n)).hom (ccm17_realShuffleChain n v)) =
    (π.f (n + 1)).hom ((((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).d (2 + n) (n + 1)).hom
      (ccm17_realShuffleChain n v)) at hcomm
  rw [hcomm]
  let F : (Fin (2 + n) → Fin 3) → (Fin (2 + n) → Fin (n + 1)) →
      ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of (Fin (2 + n) → ℝ)) B)).X (n + 1) :=
    fun a b => (π.f (n + 1)).hom (chainOfSimplex ℚ (ccm17_realProductSimplex n
      (fun j : Fin (n + 1 + 1) => a ⟨j.val, by omega⟩)
      (fun j : Fin (n + 1 + 1) => b ⟨j.val, by omega⟩) v))
  have hF := ccm17_signedFace_boundary_sum F
    (fun a b j hj => ccm17_relativeProjection_simplex_zero X B _
      (hL _ _ j (fun i => hj _)))
    (fun a b j hj => ccm17_relativeProjection_simplex_zero X B _
      (hR _ _ j (fun i => hj _)))
  unfold ccm17_realShuffleChain
  simp only [map_sum, map_smul]
  convert hF using 1
  apply Finset.sum_congr rfl
  intro s _
  rw [ccm17_realProductSimplex_boundary n _ _ (by omega)]
  simp only [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold ccm17_signedFace
  exact smul_comm _ _ _

/-- The diagonal head shift used to move the origin into the ordered shuffle simplex. -/
private def ccm17_kappa (n : ℕ) : ℝ := 1 - 1 / (2 * ((n : ℝ) + 1))

private theorem ccm17_kappa_lt_one (n : ℕ) : ccm17_kappa n < 1 := by
  unfold ccm17_kappa
  have : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  linarith

private theorem ccm17_kappa_nonneg (n : ℕ) : 0 ≤ ccm17_kappa n := by
  unfold ccm17_kappa
  have h1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact h1
  linarith

/-- The head translation vector, with zero tail. -/
private def ccm17_headShift (n : ℕ) : Fin (2 + n) → ℝ :=
  Fin.append (fun _ : Fin 2 => ccm17_kappa n) 0

/-- Points whose translates along the head shift all avoid the origin. -/
private def ccm17_shiftSupport (n : ℕ) : Set (Fin (2 + n) → ℝ) :=
  {x | ∀ s : unitInterval, x + (s : ℝ) • ccm17_headShift n ≠ 0}

open Convexity in
/-- A boundary point of the standard triangle, translated by at most a
diagonal vector of size less than one, avoids the origin. -/
private theorem ccm17_triangle_translate_ne_zero (w : StdSimplex ℝ (Fin 3)) (j : Fin 3)
    (hj : w.weights j = 0) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1) :
    standardAffineSimplex 2 w + (fun _ => c) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.add_apply, Pi.zero_apply, standardAffineSimplex] at h0 h1
  have htot := w.total_of_fintype
  rw [Fin.sum_univ_three] at htot
  have n0 : 0 ≤ w.weights 0 := w.nonneg 0
  have n1 : 0 ≤ w.weights 1 := w.nonneg 1
  have n2 : 0 ≤ w.weights 2 := w.nonneg 2
  change w.weights 0 - w.weights 2 + c = 0 at h0
  change w.weights 1 - w.weights 2 + c = 0 at h1
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hj <;> linarith

open Convexity in
private theorem ccm17_realProductSimplex_apply (n : ℕ) {m : ℕ}
    (a : Fin (m + 1) → Fin 3) (b : Fin (m + 1) → Fin (n + 1)) (v : Fin (2 + n) → ℝ)
    (t : StdSimplex ℝ (Fin (m + 1))) :
    (TopCat.of (Fin (2 + n) → ℝ)).toSSetObjEquiv _ (ccm17_realProductSimplex n a b v) t =
      Fin.append (standardAffineSimplex 2 (StdSimplex.map a t))
        (standardAffineSimplex n (StdSimplex.map b t)) + v := by
  unfold ccm17_realProductSimplex
  rw [Equiv.apply_symm_apply]
  rfl

/-- Product faces omitting a vertex of either factor lie in the shift support. -/
private theorem ccm17_realShuffle_shiftCycle (n : ℕ) :
    (((relativeChainFunctor ℚ).obj
      (TopPair.ofSubset (X := TopCat.of (Fin (2 + n) → ℝ)) (ccm17_shiftSupport n))).d (2 + n)
      ((ComplexShape.down ℕ).next (2 + n))).hom
      (((relativeChainProjection ℚ
        (TopPair.ofSubset (X := TopCat.of (Fin (2 + n) → ℝ)) (ccm17_shiftSupport n))).f
          (2 + n)).hom (ccm17_realShuffleChain n 0)) = 0 := by
  apply ccm17_realShuffleChain_cycle
  · intro a b j hj t s hs
    rw [ccm17_realProductSimplex_apply, add_zero] at hs
    have hw : (Convexity.StdSimplex.map a t).weights j = 0 := by
      rw [Convexity.StdSimplex.weights_map_apply]
      exact Finset.sum_eq_zero fun i hi => False.elim (hj i (Finset.mem_filter.mp hi).2)
    apply ccm17_triangle_translate_ne_zero _ j hw ((s : ℝ) * ccm17_kappa n)
      (mul_nonneg s.2.1 (ccm17_kappa_nonneg n))
      (lt_of_le_of_lt (mul_le_of_le_one_left (ccm17_kappa_nonneg n) s.2.2)
        (ccm17_kappa_lt_one n))
    funext i
    have := congrFun hs (Fin.castAdd n i)
    simp only [Pi.add_apply, Pi.smul_apply, Fin.append_left, ccm17_headShift,
      smul_eq_mul, Pi.zero_apply] at this
    simpa only [Pi.add_apply, Pi.zero_apply] using this
  · intro a b j hj t s hs
    rw [ccm17_realProductSimplex_apply, add_zero] at hs
    apply ccm17_affine_reparam_ne_zero b j hj t
    funext i
    have := congrFun hs (Fin.natAdd 2 i)
    simp only [Pi.add_apply, Pi.smul_apply, Fin.append_right, ccm17_headShift,
      smul_eq_mul, Pi.zero_apply, mul_zero, add_zero] at this
    simpa only [Pi.zero_apply] using this

/-- Pushing the real shuffle chain along a translation translates every simplex. -/
private theorem ccm17_realShuffleChain_translate (n : ℕ) (v w : Fin (2 + n) → ℝ)
    (g : TopCat.of (Fin (2 + n) → ℝ) ⟶ TopCat.of (Fin (2 + n) → ℝ))
    (hg : ∀ x, g x = x + w) :
    ((SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of ℚ ℚ)).f (2 + n)).hom
      (ccm17_realShuffleChain n v) = ccm17_realShuffleChain n (v + w) := by
  unfold ccm17_realShuffleChain
  simp only [map_sum, map_smul, chainOfSimplex_map]
  apply Finset.sum_congr rfl
  intro s _
  congr 2
  apply ((TopCat.of (Fin (2 + n) → ℝ)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  rw [ccm17_realProductSimplex_apply]
  change g ((TopCat.of (Fin (2 + n) → ℝ)).toSSetObjEquiv _
    (ccm17_realProductSimplex n (ccm17_shuffleLeft s) (ccm17_shuffleRight s) v) t) = _
  rw [hg, ccm17_realProductSimplex_apply, add_assoc]

/-- The head translation homotopy identifies the classes of the original and the
translated shuffle chains. -/
private theorem ccm17_realShuffle_shift_class (n : ℕ)
    (h0 : (((relativeChainFunctor ℚ).obj (puncturedPair ℝ (2 + n))).d (2 + n)
      ((ComplexShape.down ℕ).next (2 + n))).hom
      (((relativeChainProjection ℚ (puncturedPair ℝ (2 + n))).f (2 + n)).hom
        (ccm17_realShuffleChain n 0)) = 0)
    (h1 : (((relativeChainFunctor ℚ).obj (puncturedPair ℝ (2 + n))).d (2 + n)
      ((ComplexShape.down ℕ).next (2 + n))).hom
      (((relativeChainProjection ℚ (puncturedPair ℝ (2 + n))).f (2 + n)).hom
        (ccm17_realShuffleChain n (ccm17_headShift n))) = 0) :
    ccm17_chainClass (puncturedPair ℝ (2 + n)) (2 + n) (ccm17_realShuffleChain n 0) h0 =
      ccm17_chainClass (puncturedPair ℝ (2 + n)) (2 + n)
        (ccm17_realShuffleChain n (ccm17_headShift n)) h1 := by
  let X := TopCat.of (Fin (2 + n) → ℝ)
  let F : C(unitInterval × X, X) :=
    ⟨fun p => p.2 + (p.1 : ℝ) • ccm17_headShift n, by fun_prop⟩
  have hF : ∀ s, ∀ a ∈ ccm17_shiftSupport n, F (s, a) ∈ ({0}ᶜ : Set X) :=
    fun s a ha => ha s
  let H := ccm17_ofSubsetHomotopy (A := ccm17_shiftSupport n) F hF
  have e := H.relativeHomologyMap_apply_eq (R := ℚ) (2 + n)
    (ccm17_chainClass _ (2 + n) (ccm17_realShuffleChain n 0) (ccm17_realShuffle_shiftCycle n))
  have p0 := ccm17_realShuffleChain_translate n 0 (((0 : unitInterval) : ℝ) • ccm17_headShift n)
    (TopCat.ofHom ⟨fun x => F (0, x), by fun_prop⟩) (fun _ => rfl)
  have p1 := ccm17_realShuffleChain_translate n 0 (((1 : unitInterval) : ℝ) • ccm17_headShift n)
    (TopCat.ofHom ⟨fun x => F (1, x), by fun_prop⟩) (fun _ => rfl)
  simp only [Set.Icc.coe_zero, Set.Icc.coe_one, zero_smul, one_smul, zero_add,
    add_zero] at p0 p1
  rw [ccm17_chainClass_map _ _ _ _ (by
      change (((relativeChainFunctor ℚ).obj (puncturedPair ℝ (2 + n))).d (2 + n)
        ((ComplexShape.down ℕ).next (2 + n))).hom
        (((relativeChainProjection ℚ (puncturedPair ℝ (2 + n))).f (2 + n)).hom
          (((SSet.chainComplexMap (TopCat.toSSet.map
            (TopCat.ofHom ⟨fun x => F (0, x), by fun_prop⟩)) (ModuleCat.of ℚ ℚ)).f
              (2 + n)).hom (ccm17_realShuffleChain n 0))) = 0
      rw [p0]
      exact h0),
    ccm17_chainClass_map _ _ _ _ (by
      change (((relativeChainFunctor ℚ).obj (puncturedPair ℝ (2 + n))).d (2 + n)
        ((ComplexShape.down ℕ).next (2 + n))).hom
        (((relativeChainProjection ℚ (puncturedPair ℝ (2 + n))).f (2 + n)).hom
          (((SSet.chainComplexMap (TopCat.toSSet.map
            (TopCat.ofHom ⟨fun x => F (1, x), by fun_prop⟩)) (ModuleCat.of ℚ ℚ)).f
              (2 + n)).hom (ccm17_realShuffleChain n 0))) = 0
      rw [p1]
      exact h1)] at e
  refine (ccm17_chainClass_congr _ _ _ _ _ _ ?_).trans (e.trans
    (ccm17_chainClass_congr _ _ _ _ _ _ ?_))
  · exact congrArg _ p0.symm
  · exact congrArg _ p1

/-- Outside the ordered shuffle, a vertex in the first right column precedes
the last left vertex. -/
private theorem ccm17_shuffle_right_zero_left_le {n : ℕ} (s : ccm17_Shuffle n)
    (hs : s ≠ ccm17_identityShuffle n) (i : Fin (2 + n + 1))
    (hi : ccm17_shuffleRight s i = 0) : (ccm17_shuffleLeft s i).val ≤ 1 := by
  have hab : s.1.1.val < s.1.2.val := s.2
  have hv := congrArg Fin.val hi
  simp only [ccm17_shuffleRight, ccm17_shuffleLeft, Fin.val_zero] at hv ⊢
  by_contra hc
  have hb : s.1.2.val < 2 := by split_ifs at hv hc <;> omega
  apply hs
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    change s.1.1.val = 0
    omega
  · apply Fin.ext
    change s.1.2.val = 1
    omega

open Convexity in
/-- After the head shift, every shuffle simplex other than the ordered one
misses the origin. -/
private theorem ccm17_shiftedShuffle_ne_zero {n : ℕ} (s : ccm17_Shuffle n)
    (hs : s ≠ ccm17_identityShuffle n) (t : StdSimplex ℝ (Fin (2 + n + 1))) :
    Fin.append (standardAffineSimplex 2 (StdSimplex.map (ccm17_shuffleLeft s) t))
      (standardAffineSimplex n (StdSimplex.map (ccm17_shuffleRight s) t)) +
        ccm17_headShift n ≠ 0 := by
  classical
  intro h
  set w := StdSimplex.map (ccm17_shuffleLeft s) t with hw
  set u := StdSimplex.map (ccm17_shuffleRight s) t with hu
  have h0 := congrFun h (Fin.castAdd n 0)
  have h1 := congrFun h (Fin.castAdd n 1)
  simp only [Pi.add_apply, Fin.append_left, ccm17_headShift, Pi.zero_apply,
    standardAffineSimplex] at h0 h1
  change w.weights 0 - w.weights 2 + ccm17_kappa n = 0 at h0
  change w.weights 1 - w.weights 2 + ccm17_kappa n = 0 at h1
  have hall : ∀ j, u.weights j = u.weights (Fin.last n) := by
    intro j
    refine Fin.lastCases rfl (fun k => ?_) j
    have hk := congrFun h (Fin.natAdd 2 k)
    simp only [Pi.add_apply, Fin.append_right, ccm17_headShift, Pi.zero_apply,
      add_zero, standardAffineSimplex] at hk
    linarith
  have htu : ((n : ℝ) + 1) * u.weights (Fin.last n) = 1 := by
    have := u.total_of_fintype
    rw [Finset.sum_congr rfl (fun j _ => hall j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    exact this
  have htw := w.total_of_fintype
  rw [Fin.sum_univ_three] at htw
  have hle : u.weights 0 ≤ w.weights 0 + w.weights 1 := by
    rw [hu, hw, StdSimplex.weights_map_apply, StdSimplex.weights_map_apply,
      StdSimplex.weights_map_apply, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hn : 0 ≤ t.weights i := t.nonneg i
    by_cases h₁ : ccm17_shuffleRight s i = 0
    · rw [if_pos h₁]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp
        (ccm17_shuffle_right_zero_left_le s hs i h₁) with h | h
      · rw [if_pos (Fin.ext h)]
        split_ifs <;> linarith
      · have h0 : ccm17_shuffleLeft s i ≠ 0 := fun e => by
          rw [e] at h
          exact absurd h (by decide)
        rw [if_neg h0, if_pos (Fin.ext h)]
        linarith
    · rw [if_neg h₁]
      split_ifs <;> linarith
  have hk : (1 - ccm17_kappa n) * (2 * ((n : ℝ) + 1)) = 1 := by
    unfold ccm17_kappa
    field_simp
    ring
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [hall 0] at hle
  nlinarith

/-- In relative chains modulo the punctured space, the shifted shuffle chain
reduces to its ordered simplex. -/
private theorem ccm17_realShuffleChain_shift_projection (n : ℕ) :
    ((relativeChainProjection ℚ (puncturedPair ℝ (2 + n))).f (2 + n)).hom
      (ccm17_realShuffleChain n (ccm17_headShift n)) =
    ((relativeChainProjection ℚ (puncturedPair ℝ (2 + n))).f (2 + n)).hom
      (chainOfSimplex ℚ (ccm17_realProductSimplex n
        (ccm17_shuffleLeft (ccm17_identityShuffle n))
        (ccm17_shuffleRight (ccm17_identityShuffle n)) (ccm17_headShift n))) := by
  classical
  unfold ccm17_realShuffleChain
  rw [map_sum, Finset.sum_eq_single (ccm17_identityShuffle n)]
  · rw [map_smul]
    simp only [ccm17_identityShuffle, Nat.reduceAdd, Nat.sub_self, pow_zero, one_smul]
  · intro s _ hs
    rw [map_smul, ccm17_relativeProjection_simplex_zero _ _ _ (fun t => by
      rw [ccm17_realProductSimplex_apply]
      exact ccm17_shiftedShuffle_ne_zero s hs t), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

open Convexity in
private theorem ccm17_identityLeft_weights (n : ℕ) (t : StdSimplex ℝ (Fin (2 + n + 1))) :
    (StdSimplex.map (ccm17_shuffleLeft (ccm17_identityShuffle n)) t).weights 0 =
      t.weights ⟨0, by omega⟩ ∧
    (StdSimplex.map (ccm17_shuffleLeft (ccm17_identityShuffle n)) t).weights 1 =
      t.weights ⟨1, by omega⟩ := by
  classical
  constructor
  · rw [StdSimplex.weights_map_apply, Finset.sum_filter, Finset.sum_eq_single ⟨0, by omega⟩]
    · rw [if_pos]
      apply Fin.ext
      simp [ccm17_shuffleLeft, ccm17_identityShuffle]
    · intro i _ hi
      rw [if_neg]
      intro he
      apply hi
      have hv := congrArg Fin.val he
      simp only [ccm17_shuffleLeft, ccm17_identityShuffle, Fin.val_zero] at hv
      apply Fin.ext
      change i.val = 0
      split_ifs at hv <;> omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [StdSimplex.weights_map_apply, Finset.sum_filter, Finset.sum_eq_single ⟨1, by omega⟩]
    · rw [if_pos]
      apply Fin.ext
      simp [ccm17_shuffleLeft, ccm17_identityShuffle]
    · intro i _ hi
      rw [if_neg]
      intro he
      apply hi
      have hv := congrArg Fin.val he
      simp only [ccm17_shuffleLeft, ccm17_identityShuffle, Fin.val_one] at hv
      apply Fin.ext
      change i.val = 1
      split_ifs at hv <;> omega
    · intro h
      exact absurd (Finset.mem_univ _) h

open Convexity in
private theorem ccm17_identityRight_weights_zero (n : ℕ)
    (t : StdSimplex ℝ (Fin (2 + n + 1))) :
    (StdSimplex.map (ccm17_shuffleRight (ccm17_identityShuffle n)) t).weights 0 =
      t.weights ⟨0, by omega⟩ + t.weights ⟨1, by omega⟩ + t.weights ⟨2, by omega⟩ := by
  classical
  rw [StdSimplex.weights_map_apply, Finset.sum_filter]
  rw [← Finset.sum_subset (Finset.subset_univ
    ({⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin (2 + n + 1))))]
  · rw [Finset.sum_insert (by simp [Fin.ext_iff]), Finset.sum_insert (by simp [Fin.ext_iff]),
      Finset.sum_singleton]
    simp only [ccm17_shuffleRight, ccm17_shuffleLeft, ccm17_identityShuffle]
    simp
    ring
  · intro i _ hi
    rw [if_neg]
    intro he
    apply hi
    have hv := congrArg Fin.val he
    simp only [ccm17_shuffleRight, ccm17_shuffleLeft, ccm17_identityShuffle,
      Fin.val_zero] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    split_ifs at hv <;> omega

open Convexity in
private theorem ccm17_identityRight_weights_succ (n : ℕ)
    (t : StdSimplex ℝ (Fin (2 + n + 1))) (j : Fin n) :
    (StdSimplex.map (ccm17_shuffleRight (ccm17_identityShuffle n)) t).weights j.succ =
      t.weights ⟨j.val + 3, by omega⟩ := by
  classical
  rw [StdSimplex.weights_map_apply, Finset.sum_filter, Finset.sum_eq_single ⟨j.val + 3, by omega⟩]
  · rw [if_pos]
    apply Fin.ext
    simp only [ccm17_shuffleRight, ccm17_shuffleLeft, ccm17_identityShuffle, Fin.val_succ]
    split_ifs <;> omega
  · intro i _ hi
    rw [if_neg]
    intro he
    apply hi
    have hv := congrArg Fin.val he
    simp only [ccm17_shuffleRight, ccm17_shuffleLeft, ccm17_identityShuffle,
      Fin.val_succ] at hv
    apply Fin.ext
    change i.val = j.val + 3
    split_ifs at hv <;> omega
  · intro h
    exact absurd (Finset.mem_univ _) h


/-- The real inequalities behind the straight line from the shifted ordered
shuffle simplex to the fixed simplex. -/
private theorem ccm17_orderedLine_algebra (n : ℕ) (s κ a b c T : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (na : 0 ≤ a) (nb : 0 ≤ b) (nc : 0 ≤ c) (nT : 0 ≤ T)
    (hκ1 : κ < 1) (hκh : 1 / 2 ≤ κ) (hκ : (1 - κ) * (2 * ((n : ℝ) + 1)) = 1)
    (E0 : (1 - s) * (a - (1 - a - b) + κ) + s * (a - T) = 0)
    (E1 : (1 - s) * (b - (1 - a - b) + κ) + s * (b - T) = 0)
    (hsum : a + b + c + n * T = 1)
    (hc0 : 0 < n → c - T + (1 - s) * (a + b) = 0) (hc0' : n = 0 → c = T)
    (hk : a = 0 ∨ b = 0 ∨ c = 0 ∨ T = 0) : False := by
  have hab : a = b := by nlinarith
  subst hab
  have hk' : a = 0 ∨ c = 0 ∨ T = 0 := by
    rcases hk with h | h | h | h
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hr0 : 0 ≤ 1 - s := by linarith
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hcT := hc0' hn
    have hn' : (n : ℝ) = 0 := by exact_mod_cast hn
    rw [hn', zero_mul, add_zero] at hsum
    subst hcT
    rcases hk' with h0 | h0 | h0
    · subst h0
      nlinarith [mul_nonneg hr0 (by linarith : (0 : ℝ) ≤ 1 - κ)]
    · subst h0
      nlinarith [mul_nonneg hr0 (by linarith : (0 : ℝ) ≤ 3 * a - 1 + κ)]
    · subst h0
      nlinarith [mul_nonneg hr0 (by linarith : (0 : ℝ) ≤ 3 * a - 1 + κ)]
  · have hcT := hc0 hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rcases hk' with h0 | h0 | h0
    · subst h0
      have e1 : (1 - s) * (1 - κ) = 0 := by
        nlinarith [mul_nonneg hr0 (by linarith : (0 : ℝ) ≤ 1 - κ), mul_nonneg hs0 nT]
      have hs : 1 - s = 0 := by
        rcases mul_eq_zero.mp e1 with e | e
        · exact e
        · linarith
      have hs' : s = 1 := by linarith
      subst hs'
      have hT0 : T = 0 := by linarith
      subst hT0
      nlinarith
    · subst h0
      have hTa : T = 2 * (1 - s) * a := by linarith
      subst hTa
      have e1 : a * (1 + 2 * (1 - s) ^ 2) = (1 - s) * (1 - κ) := by
        linear_combination E0
      have e2 : a * (2 + 2 * n * (1 - s)) = 1 := by linear_combination hsum
      have e3 : ((n : ℝ) + 1) * (1 + 2 * (1 - s) ^ 2) = (1 - s) * (1 + n * (1 - s)) := by
        linear_combination (-((n : ℝ) + 1) * (1 + 2 * (1 - s) ^ 2)) * e2 +
          (((n : ℝ) + 1) * (2 + 2 * n * (1 - s))) * e1 + ((1 - s) * (1 + n * (1 - s))) * hκ
      nlinarith [mul_nonneg hn0 (sq_nonneg (1 - s)), sq_nonneg (1 - s),
        mul_nonneg hn0 hr0, mul_nonneg hn0 hs0]
    · subst h0
      have h1 : c = 0 := by nlinarith [mul_nonneg hr0 na]
      have h2 : (1 - s) * a = 0 := by nlinarith [mul_nonneg hr0 na]
      subst h1
      have ha2 : a = 1 / 2 := by linarith
      subst ha2
      have hs : 1 - s = 0 := by linarith
      nlinarith

open Convexity in
/-- The straight line from the head-shifted ordered shuffle simplex to the fixed
real simplex avoids the origin on every face. -/
private theorem ccm17_orderedLine_ne_zero (n : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (t : StdSimplex ℝ (Fin (2 + n + 1))) (k : Fin (2 + n + 1)) (hk : t.weights k = 0) :
    (1 - s) • (Fin.append
      (standardAffineSimplex 2 (StdSimplex.map (ccm17_shuffleLeft (ccm17_identityShuffle n)) t))
      (standardAffineSimplex n (StdSimplex.map (ccm17_shuffleRight (ccm17_identityShuffle n)) t)) +
        ccm17_headShift n) + s • standardAffineSimplex (2 + n) t ≠ 0 := by
  intro h
  set u := StdSimplex.map (ccm17_shuffleRight (ccm17_identityShuffle n)) t with hu
  obtain ⟨W0, W1⟩ := ccm17_identityLeft_weights n t
  have htw := (StdSimplex.map (ccm17_shuffleLeft (ccm17_identityShuffle n)) t).total_of_fintype
  rw [Fin.sum_univ_three, W0, W1] at htw
  have E0 := congrFun h (Fin.castAdd n 0)
  have E1 := congrFun h (Fin.castAdd n 1)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.append_left, ccm17_headShift,
    standardAffineSimplex] at E0 E1
  change (1 - s) * ((StdSimplex.map (ccm17_shuffleLeft (ccm17_identityShuffle n)) t).weights 0 -
    (StdSimplex.map (ccm17_shuffleLeft (ccm17_identityShuffle n)) t).weights 2 +
    ccm17_kappa n) + s * (t.weights ⟨0, by omega⟩ - t.weights (Fin.last (2 + n))) = 0 at E0
  change (1 - s) * ((StdSimplex.map (ccm17_shuffleLeft (ccm17_identityShuffle n)) t).weights 1 -
    (StdSimplex.map (ccm17_shuffleLeft (ccm17_identityShuffle n)) t).weights 2 +
    ccm17_kappa n) + s * (t.weights ⟨1, by omega⟩ - t.weights (Fin.last (2 + n))) = 0 at E1
  have hw2 : (StdSimplex.map (ccm17_shuffleLeft (ccm17_identityShuffle n)) t).weights 2 =
      1 - t.weights ⟨0, by omega⟩ - t.weights ⟨1, by omega⟩ := by linarith
  rw [W0, hw2] at E0
  rw [W1, hw2] at E1
  have tail : ∀ j : Fin n, (1 - s) * (u.weights j.castSucc - u.weights (Fin.last n)) +
      s * (t.weights ⟨j.val + 2, by omega⟩ - t.weights (Fin.last (2 + n))) = 0 := by
    intro j
    have := congrFun h (Fin.natAdd 2 j)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.append_right, ccm17_headShift,
      standardAffineSimplex, Pi.zero_apply, add_zero] at this
    rwa [show (Fin.natAdd 2 j).castSucc = ⟨j.val + 2, by omega⟩ from
      Fin.ext (by simp only [Fin.val_castSucc, Fin.val_natAdd]; omega)] at this
  have ulast : ∀ j : Fin n, u.weights (Fin.last n) = t.weights (Fin.last (2 + n)) := by
    intro j
    have hj := j.isLt
    have e : Fin.last n = Fin.succ ⟨n - 1, by omega⟩ :=
      Fin.ext (by simp only [Fin.val_last, Fin.val_succ]; omega)
    rw [e, hu, ccm17_identityRight_weights_succ]
    exact congrArg t.weights (Fin.ext (by simp only [Fin.val_last]; omega))
  have hT3 : ∀ j : Fin n, t.weights ⟨j.val + 3, by omega⟩ = t.weights (Fin.last (2 + n)) := by
    intro j
    by_cases hj : j.val + 1 < n
    · have e := tail ⟨j.val + 1, hj⟩
      have e' : (⟨j.val + 1, hj⟩ : Fin n).castSucc = Fin.succ ⟨j.val, by omega⟩ := Fin.ext rfl
      rw [e', hu, ccm17_identityRight_weights_succ, ← hu, ulast j] at e
      have e'' : t.weights ⟨j.val + 1 + 2, by omega⟩ = t.weights ⟨j.val + 3, by omega⟩ := rfl
      rw [e''] at e
      linarith
    · have hj' := j.isLt
      exact congrArg t.weights (Fin.ext (by simp only [Fin.val_last]; omega))
  have hsum : t.weights ⟨0, by omega⟩ + t.weights ⟨1, by omega⟩ + t.weights ⟨2, by omega⟩ +
      n * t.weights (Fin.last (2 + n)) = 1 := by
    have := u.total_of_fintype
    rw [Fin.sum_univ_succ, hu, ccm17_identityRight_weights_zero] at this
    simp only [ccm17_identityRight_weights_succ, hT3, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have hc0 : 0 < n → t.weights ⟨2, by omega⟩ - t.weights (Fin.last (2 + n)) +
      (1 - s) * (t.weights ⟨0, by omega⟩ + t.weights ⟨1, by omega⟩) = 0 := by
    intro hn
    have e := tail ⟨0, hn⟩
    have e' : (⟨0, hn⟩ : Fin n).castSucc = 0 := rfl
    rw [e', hu, ccm17_identityRight_weights_zero, ← hu, ulast ⟨0, hn⟩] at e
    linarith
  have hc0' : n = 0 → t.weights ⟨2, by omega⟩ = t.weights (Fin.last (2 + n)) := by
    intro hn
    subst hn
    rfl
  have hk' : t.weights ⟨0, by omega⟩ = 0 ∨ t.weights ⟨1, by omega⟩ = 0 ∨
      t.weights ⟨2, by omega⟩ = 0 ∨ t.weights (Fin.last (2 + n)) = 0 := by
    have hkv := k.isLt
    by_cases k0 : k.val = 0
    · left; rw [← hk]; exact congrArg t.weights (Fin.ext k0.symm)
    by_cases k1 : k.val = 1
    · right; left; rw [← hk]; exact congrArg t.weights (Fin.ext k1.symm)
    by_cases k2 : k.val = 2
    · right; right; left; rw [← hk]; exact congrArg t.weights (Fin.ext k2.symm)
    right; right; right
    rw [← hT3 ⟨k.val - 3, by omega⟩, ← hk]
    exact congrArg t.weights (Fin.ext (by simp only; omega))
  have hκ : (1 - ccm17_kappa n) * (2 * ((n : ℝ) + 1)) = 1 := by
    unfold ccm17_kappa
    field_simp
    ring
  have hκh : (1 : ℝ) / 2 ≤ ccm17_kappa n := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    unfold ccm17_kappa
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2)] at *
    have h2 : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith
    linarith
  exact ccm17_orderedLine_algebra n s (ccm17_kappa n) _ _ _ _ hs0 hs1 (t.nonneg _) (t.nonneg _)
    (t.nonneg _) (t.nonneg _) (ccm17_kappa_lt_one n) hκh hκ E0 E1 hsum hc0 hc0' hk'

/-- Pair maps preserve explicit relative cycles. -/
private theorem ccm17_chainCycle_map {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ)
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

/-- The boundary of the standard topological simplex. -/
private def ccm17_simplexBoundary (d : ℕ) : Set (Convexity.StdSimplex ℝ (Fin (d + 1))) :=
  {t | ∃ k, t.weights k = 0}

open scoped Simplicial in
/-- The identity singular simplex of the standard topological simplex. -/
private def ccm17_identitySimplex (d : ℕ) :
    (TopCat.toSSet.obj (TopCat.of (Convexity.StdSimplex ℝ (Fin (d + 1))))) _⦋d⦌ :=
  ((TopCat.of (Convexity.StdSimplex ℝ (Fin (d + 1)))).toSSetObjEquiv _).symm
    (ContinuousMap.id _)

/-- The identity simplex is a relative cycle modulo the boundary of the simplex. -/
private theorem ccm17_identitySimplex_cycle (d : ℕ) :
    (((relativeChainFunctor ℚ).obj (TopPair.ofSubset
      (X := TopCat.of (Convexity.StdSimplex ℝ (Fin (d + 1)))) (ccm17_simplexBoundary d))).d d
      ((ComplexShape.down ℕ).next d)).hom
      (((relativeChainProjection ℚ (TopPair.ofSubset
        (X := TopCat.of (Convexity.StdSimplex ℝ (Fin (d + 1)))) (ccm17_simplexBoundary d))).f
          d).hom (chainOfSimplex ℚ (ccm17_identitySimplex d))) = 0 := by
  cases d with
  | zero =>
    rw [HomologicalComplex.shape _ 0 _ (by simp), ModuleCat.hom_zero, LinearMap.zero_apply]
  | succ m =>
    rw [ChainComplex.next_nat_succ]
    let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (m + 1 + 1)))
    let π := relativeChainProjection ℚ (TopPair.ofSubset (X := X) (ccm17_simplexBoundary (m + 1)))
    have hcomm := ConcreteCategory.congr_hom (π.comm (m + 1) m)
      (chainOfSimplex ℚ (ccm17_identitySimplex (m + 1)))
    change (((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X)
      (ccm17_simplexBoundary (m + 1)))).d (m + 1) m).hom
      ((π.f (m + 1)).hom (chainOfSimplex ℚ (ccm17_identitySimplex (m + 1)))) =
      (π.f m).hom (boundary ℚ m (chainOfSimplex ℚ (ccm17_identitySimplex (m + 1))))
      at hcomm
    rw [hcomm, boundary_chainOfSimplex, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul, ccm17_relativeProjection_simplex_zero _ _ _ (fun t => by
      change ∃ k, (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i
        (ccm17_identitySimplex (m + 1))) t).weights k = 0
      exact ⟨i, stdSimplex_map_succAbove_self_zero m i t⟩), smul_zero]

open scoped Simplicial in
/-- Pushing the identity simplex along a continuous map gives that map as a simplex. -/
private theorem ccm17_identitySimplex_push (d : ℕ) (X : TopCat.{0})
    (f : C(Convexity.StdSimplex ℝ (Fin (d + 1)), X)) :
    (TopCat.toSSet.map (X := TopCat.of (Convexity.StdSimplex ℝ (Fin (d + 1))))
      (TopCat.ofHom f)).app _ (ccm17_identitySimplex d) = (X.toSSetObjEquiv _).symm f := by
  apply (X.toSSetObjEquiv _).injective
  rw [Equiv.apply_symm_apply]
  rfl

open scoped Simplicial in
/-- A simplex whose boundary lies in the subspace is a relative cycle. -/
private theorem ccm17_simplex_cycle (d : ℕ) (X : TopCat.{0}) (B : Set X)
    (σ : (TopCat.toSSet.obj X) _⦋d⦌)
    (hσ : ∀ t ∈ ccm17_simplexBoundary d, X.toSSetObjEquiv _ σ t ∈ B) :
    (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).d d
      ((ComplexShape.down ℕ).next d)).hom
      (((relativeChainProjection ℚ (TopPair.ofSubset B)).f d).hom (chainOfSimplex ℚ σ)) = 0 := by
  have h := ccm17_chainCycle_map
    (TopPair.ofSubsetHom (B := B) (TopCat.ofHom (X.toSSetObjEquiv _ σ)) hσ) d _
    (ccm17_identitySimplex_cycle d)
  rw [chainOfSimplex_map] at h
  change (((relativeChainFunctor ℚ).obj (TopPair.ofSubset B)).d d
      ((ComplexShape.down ℕ).next d)).hom
      (((relativeChainProjection ℚ (TopPair.ofSubset B)).f d).hom (chainOfSimplex ℚ
        ((TopCat.toSSet.map (TopCat.ofHom (X.toSSetObjEquiv _ σ))).app _
          (ccm17_identitySimplex d)))) = 0 at h
  rwa [ccm17_identitySimplex_push, Equiv.symm_apply_apply] at h

/-- The straight-line homotopy identifies the class of the shifted ordered
simplex with the fixed real local class. -/
private theorem ccm17_orderedSimplex_class (n : ℕ)
    (h1 : (((relativeChainFunctor ℚ).obj (puncturedPair ℝ (2 + n))).d (2 + n)
      ((ComplexShape.down ℕ).next (2 + n))).hom
      (((relativeChainProjection ℚ (puncturedPair ℝ (2 + n))).f (2 + n)).hom
        (chainOfSimplex ℚ (ccm17_realProductSimplex n
          (ccm17_shuffleLeft (ccm17_identityShuffle n))
          (ccm17_shuffleRight (ccm17_identityShuffle n)) (ccm17_headShift n)))) = 0)
    (h2 : (((relativeChainFunctor ℚ).obj (puncturedPair ℝ (2 + n))).d (2 + n)
      ((ComplexShape.down ℕ).next (2 + n))).hom
      (((relativeChainProjection ℚ (puncturedPair ℝ (2 + n))).f (2 + n)).hom
        (chainOfSimplex ℚ (standardSingularSimplex (2 + n)))) = 0) :
    ccm17_chainClass (puncturedPair ℝ (2 + n)) (2 + n)
      (chainOfSimplex ℚ (ccm17_realProductSimplex n
        (ccm17_shuffleLeft (ccm17_identityShuffle n))
        (ccm17_shuffleRight (ccm17_identityShuffle n)) (ccm17_headShift n))) h1 =
    ccm17_chainClass (puncturedPair ℝ (2 + n)) (2 + n)
      (chainOfSimplex ℚ (standardSingularSimplex (2 + n))) h2 := by
  let D := TopCat.of (Convexity.StdSimplex ℝ (Fin (2 + n + 1)))
  let X := TopCat.of (Fin (2 + n) → ℝ)
  let Ψ : C(Convexity.StdSimplex ℝ (Fin (2 + n + 1)), X) :=
    X.toSSetObjEquiv _ (ccm17_realProductSimplex n
      (ccm17_shuffleLeft (ccm17_identityShuffle n))
      (ccm17_shuffleRight (ccm17_identityShuffle n)) (ccm17_headShift n))
  let G : C(unitInterval × D, X) :=
    ⟨fun p => (1 - (p.1 : ℝ)) • Ψ p.2 + (p.1 : ℝ) • standardAffineSimplex (2 + n) p.2, by
      fun_prop⟩
  have hG : ∀ s, ∀ t ∈ ccm17_simplexBoundary (2 + n), G (s, t) ∈ ({0}ᶜ : Set X) := by
    rintro s t ⟨k, hk⟩
    change (1 - (s : ℝ)) • Ψ t + (s : ℝ) • standardAffineSimplex (2 + n) t ≠ 0
    have hΨ : Ψ t = _ := ccm17_realProductSimplex_apply n _ _ _ t
    rw [hΨ]
    exact ccm17_orderedLine_ne_zero n s s.2.1 s.2.2 t k hk
  let H := ccm17_ofSubsetHomotopy (A := ccm17_simplexBoundary (2 + n)) G hG
  have e := H.relativeHomologyMap_apply_eq (R := ℚ) (2 + n)
    (ccm17_chainClass _ (2 + n) (chainOfSimplex ℚ (ccm17_identitySimplex (2 + n)))
      (ccm17_identitySimplex_cycle (2 + n)))
  rw [ccm17_chainClass_map _ _ _ _ (ccm17_chainCycle_map _ _ _
      (ccm17_identitySimplex_cycle (2 + n))),
    ccm17_chainClass_map _ _ _ _ (ccm17_chainCycle_map _ _ _
      (ccm17_identitySimplex_cycle (2 + n)))] at e
  refine (ccm17_chainClass_congr _ _ _ _ _ _ ?_).trans (e.trans
    (ccm17_chainClass_congr _ _ _ _ _ _ ?_))
  · apply congrArg
    rw [chainOfSimplex_map]
    congr 1
    symm
    erw [ccm17_identitySimplex_push]
    apply (X.toSSetObjEquiv _).injective
    rw [Equiv.apply_symm_apply]
    apply ContinuousMap.ext
    intro t
    change (1 - ((0 : unitInterval) : ℝ)) • Ψ t +
      ((0 : unitInterval) : ℝ) • standardAffineSimplex (2 + n) t = Ψ t
    simp
  · apply congrArg
    rw [chainOfSimplex_map]
    congr 1
    erw [ccm17_identitySimplex_push]
    apply (X.toSSetObjEquiv _).injective
    rw [Equiv.apply_symm_apply]
    apply ContinuousMap.ext
    intro t
    change (1 - ((1 : unitInterval) : ℝ)) • Ψ t +
      ((1 : unitInterval) : ℝ) • standardAffineSimplex (2 + n) t = standardAffineSimplex (2 + n) t
    simp

private theorem ccm17_standardSingularSimplex_apply (d : ℕ)
    (t : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    (TopCat.of (Fin d → ℝ)).toSSetObjEquiv _ (standardSingularSimplex d) t =
      standardAffineSimplex d t := by
  change ((puncturedPair ℝ d).fst.toSSetObjEquiv _ (standardSingularSimplex d)) t = _
  unfold standardSingularSimplex
  rw [Equiv.apply_symm_apply]
  rfl

/-- The signed real shuffle chain represents the fixed real local class in
dimension two plus `n`, with coefficient one. -/
private theorem ccm17_realShuffle_class (n : ℕ)
    (h0 : (((relativeChainFunctor ℚ).obj (puncturedPair ℝ (2 + n))).d (2 + n)
      ((ComplexShape.down ℕ).next (2 + n))).hom
      (((relativeChainProjection ℚ (puncturedPair ℝ (2 + n))).f (2 + n)).hom
        (ccm17_realShuffleChain n 0)) = 0) :
    ccm17_chainClass (puncturedPair ℝ (2 + n)) (2 + n) (ccm17_realShuffleChain n 0) h0 =
      standardLocalClass ℚ (2 + n) := by
  let X := TopCat.of (Fin (2 + n) → ℝ)
  have hσ := ccm17_simplex_cycle (2 + n) X ({0}ᶜ : Set X)
    (ccm17_realProductSimplex n (ccm17_shuffleLeft (ccm17_identityShuffle n))
      (ccm17_shuffleRight (ccm17_identityShuffle n)) (ccm17_headShift n))
    (fun t ⟨k, hk⟩ => by
      rw [ccm17_realProductSimplex_apply]
      have := ccm17_orderedLine_ne_zero n 0 le_rfl zero_le_one t k hk
      exact Set.mem_compl_singleton_iff.mpr
        (by simpa only [sub_zero, one_smul, zero_smul, add_zero] using this))
  have hstd := ccm17_simplex_cycle (2 + n) X ({0}ᶜ : Set X)
    (standardSingularSimplex (2 + n))
    (fun t ⟨k, hk⟩ => by
      rw [ccm17_standardSingularSimplex_apply]
      exact standardAffineSimplex_ne_zero_of_coord_zero _ t k hk)
  have hproj := ccm17_realShuffleChain_shift_projection n
  have h1 : (((relativeChainFunctor ℚ).obj (puncturedPair ℝ (2 + n))).d (2 + n)
      ((ComplexShape.down ℕ).next (2 + n))).hom
      (((relativeChainProjection ℚ (puncturedPair ℝ (2 + n))).f (2 + n)).hom
        (ccm17_realShuffleChain n (ccm17_headShift n))) = 0 := by
    rw [hproj]
    exact hσ
  rw [ccm17_realShuffle_shift_class n h0 h1,
    ccm17_chainClass_congr _ _ _ _ h1 hσ hproj, ccm17_orderedSimplex_class n hσ hstd,
    ← ccm17_standardLocalClass_eq_chainClass]

private theorem ccm17_complexRealHomeomorph_apply (n : ℕ) (z : Fin n → ℂ) (a : Fin n)
    (b : Fin 2) :
    complexRealHomeomorph n z (finProdFinEquiv (a, b)) = ![(z a).re, (z a).im] b := by
  simp [complexRealHomeomorph, Complex.piCoordCLE, Complex.piBasisOneI,
    Module.Basis.smulTower'_repr_mk, Complex.coe_basisOneI_repr]

/-- Consecutive real coordinates of the block map are the concatenated real coordinates. -/
private theorem ccm17_complexBlock_coordinates (q : ℕ)
    (x : Fin 2 → ℝ) (y : Fin (q * 2) → ℝ) (i : Fin ((q + 1) * 2)) :
    complexRealHomeomorph (q + 1) (ccm17_complexBlock q (x, y)) i =
      Fin.append x y (Fin.cast (by ring) i) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [ccm17_complexRealHomeomorph_apply]
  refine Fin.cases ?_ (fun a => ?_) a
  · have hx := ccm17_complexRealHomeomorph_apply 1
      ((complexRealHomeomorph 1).symm x) 0 b
    rw [Homeomorph.apply_symm_apply] at hx
    have hi : (Fin.cast (by ring) (finProdFinEquiv ((0 : Fin (q + 1)), b)) : Fin (2 + q * 2)) =
        Fin.castAdd (q * 2) (finProdFinEquiv ((0 : Fin 1), b)) := Fin.ext (by
      simp [finProdFinEquiv])
    rw [hi, Fin.append_left, hx]
    rfl
  · have hy := ccm17_complexRealHomeomorph_apply q ((complexRealHomeomorph q).symm y) a b
    rw [Homeomorph.apply_symm_apply] at hy
    have hi : (Fin.cast (by ring) (finProdFinEquiv (a.succ, b)) : Fin (2 + q * 2)) =
        Fin.natAdd 2 (finProdFinEquiv (a, b)) := Fin.ext (by
      simp [finProdFinEquiv]
      ring)
    rw [hi, Fin.append_right, hy]
    rfl

/-- Reindexing real coordinates along an equality of dimensions. -/
private def ccm17_reindexPair (d d' : ℕ) (j : d' = d) :
    puncturedPair ℝ d ⟶ puncturedPair ℝ d' :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨fun x => x ∘ Fin.cast j, by fun_prop⟩) (fun x hx h => hx (by
    funext i
    have := congrFun h (Fin.cast j.symm i)
    simpa using this))

private theorem ccm17_reindexPair_standardLocalClass (d d' : ℕ) (j : d' = d) :
    relativeHomologyMap ℚ d (ccm17_reindexPair d d' j) (standardLocalClass ℚ d) =
      j ▸ standardLocalClass ℚ d' := by
  subst j
  have h : ccm17_reindexPair d' d' rfl = 𝟙 _ := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext a
      rfl
    · ext x
      rfl
  rw [h, relativeHomologyMap_id]
  rfl

private theorem ccm17_relativeHomologyMap_cast {P Q : TopPair.{0}} (f : P ⟶ Q) {m n : ℕ}
    (h : m = n) (x : RelativeHomology ℚ P m) :
    relativeHomologyMap ℚ n f (h ▸ x) = h ▸ relativeHomologyMap ℚ m f x := by
  subst h
  rfl

private theorem ccm17_homology_cast_trans {P : TopPair.{0}} {m n p : ℕ}
    (h₁ : m = n) (h₂ : n = p) (h : m = p) (x : RelativeHomology ℚ P m) :
    h₂ ▸ h₁ ▸ x = h ▸ x := by
  subst h₁
  subst h₂
  rfl

private theorem ccm17_iso_homology_cast {P Q : TopPair.{0}} (e : P ≅ Q) {m n : ℕ}
    (k : m = n) (z : RelativeHomology ℚ Q m) (w : RelativeHomology ℚ P n)
    (h : relativeHomologyMap ℚ n e.hom w = k ▸ z) :
    k ▸ relativeHomologyMap ℚ m e.inv z = w := by
  subst k
  change relativeHomologyMap ℚ m e.hom w = z at h
  change relativeHomologyMap ℚ m e.inv z = w
  rw [← h]
  change ((relativeHomologyMap ℚ m e.inv).comp (relativeHomologyMap ℚ m e.hom)) w = w
  rw [← relativeHomologyMap_comp, e.hom_inv_id, relativeHomologyMap_id]
  rfl

/-- The real shuffle chain is a relative cycle modulo the punctured space. -/
private theorem ccm17_realShuffle_punctCycle (n : ℕ) :
    (((relativeChainFunctor ℚ).obj (puncturedPair ℝ (2 + n))).d (2 + n)
      ((ComplexShape.down ℕ).next (2 + n))).hom
      (((relativeChainProjection ℚ (puncturedPair ℝ (2 + n))).f (2 + n)).hom
        (ccm17_realShuffleChain n 0)) = 0 := by
  apply ccm17_realShuffleChain_cycle
  · intro a b j hj t hs
    rw [ccm17_realProductSimplex_apply, add_zero] at hs
    apply ccm17_affine_reparam_ne_zero a j hj t
    funext i
    have := congrFun hs (Fin.castAdd n i)
    simpa only [Fin.append_left, Pi.zero_apply] using this
  · intro a b j hj t hs
    rw [ccm17_realProductSimplex_apply, add_zero] at hs
    apply ccm17_affine_reparam_ne_zero b j hj t
    funext i
    have := congrFun hs (Fin.natAdd 2 i)
    simpa only [Fin.append_right, Pi.zero_apply] using this

/-- The transported complex shuffle chain is a relative cycle modulo the
complement of the intersection support. -/
private theorem ccm17_complexShuffleChain_relativeCycle (q : ℕ) :
    let Y := TopCat.of (Fin (q + 1) → ℂ)
    let S := ccm17_zeroSupport Y 1 (ccm17_head q)
    let T := ccm17_zeroSupport Y q (ccm17_tail q)
    (((relativeChainFunctor ℚ).obj (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ)).d
      (2 + q * 2) ((ComplexShape.down ℕ).next (2 + q * 2))).hom
      (((relativeChainProjection ℚ (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ)).f
        (2 + q * 2)).hom (ccm17_complexShuffleChain q)) = 0 := by
  intro Y S T
  have hfac := congrArg (fun g => g.f (2 + q * 2))
    (cokernel.π_desc _ (relativeChainProjection ℚ (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ))
      _ : ccm14_smallProjection Y S T ≫ ccm14_relativeComparison Y S T = _)
  let w := ShortComplex.moduleCatCycleMap
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) (2 + q * 2)).map
      (ccm14_relativeComparison Y S T)) (ccm17_smallShuffleCycle q)
  have hval : w.1 = ((relativeChainProjection ℚ
      (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ)).f (2 + q * 2)).hom
        (ccm17_complexShuffleChain q) :=
    ConcreteCategory.congr_hom hfac (ccm17_complexShuffleChain q)
  rw [← hval]
  exact w.2

/-- The shuffle homology class is the class of its explicit chain modulo the
complement of the intersection support. -/
private theorem ccm17_shuffleHomologyClass_eq_chainClass (q : ℕ) :
    ccm17_shuffleHomologyClass q = ccm17_chainClass _ (2 + q * 2)
      (ccm17_complexShuffleChain q) (ccm17_complexShuffleChain_relativeCycle q) := by
  let Y := TopCat.of (Fin (q + 1) → ℂ)
  let S := ccm17_zeroSupport Y 1 (ccm17_head q)
  let T := ccm17_zeroSupport Y q (ccm17_tail q)
  unfold ccm17_shuffleHomologyClass ccm17_chainClass
  refine (ShortComplex.moduleCatHomologyClass_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) (2 + q * 2)).map
      (ccm14_relativeComparison Y S T)) _).trans ?_
  congr 1
  apply Subtype.ext
  have hfac := congrArg (fun g => g.f (2 + q * 2))
    (cokernel.π_desc _ (relativeChainProjection ℚ (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ))
      _ : ccm14_smallProjection Y S T ≫ ccm14_relativeComparison Y S T = _)
  exact ConcreteCategory.congr_hom hfac (ccm17_complexShuffleChain q)

/-- After the identity of supports and the consecutive real coordinates, the
complex shuffle chain is the reindexed real shuffle chain. -/
private theorem ccm17_complexShuffleChain_real (q : ℕ) :
    ((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst
      (ccm17_intersectionPair q ≫ (standardComplexRealPairIso (q + 1)).hom)))
      (ModuleCat.of ℚ ℚ)).f (2 + q * 2)).hom (ccm17_complexShuffleChain q) =
    ((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst
      (ccm17_reindexPair (2 + q * 2) ((q + 1) * 2) (by ring))))
      (ModuleCat.of ℚ ℚ)).f (2 + q * 2)).hom (ccm17_realShuffleChain (q * 2) 0) := by
  rw [ccm17_complexShuffleChain_eq_sum]
  unfold ccm17_realShuffleChain
  simp only [map_sum, map_smul, chainOfSimplex_map]
  apply Finset.sum_congr rfl
  intro s _
  congr 2
  apply ((TopCat.of (Fin ((q + 1) * 2) → ℝ)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  funext i
  change complexRealHomeomorph (q + 1) (ccm17_complexBlock q
    (standardAffineSimplex 2 (Convexity.StdSimplex.map (ccm17_shuffleLeft s) t),
      standardAffineSimplex (q * 2) (Convexity.StdSimplex.map (ccm17_shuffleRight s) t))) i =
    ((TopCat.of (Fin (2 + q * 2) → ℝ)).toSSetObjEquiv _ (ccm17_realProductSimplex (q * 2)
      (ccm17_shuffleLeft s) (ccm17_shuffleRight s) 0) t) (Fin.cast (by ring) i)
  rw [ccm17_realProductSimplex_apply, add_zero, ccm17_complexBlock_coordinates]

/-- The shuffle class, pushed to the punctured coordinate space, is the fixed
complex local class with coefficient one. -/
private theorem ccm17_shuffleHomologyClass_standard (q : ℕ) :
    relativeHomologyMap ℚ (2 + q * 2) (ccm17_intersectionPair q) (ccm17_shuffleHomologyClass q) =
      (show 2 * (q + 1) = 2 + q * 2 by ring) ▸ standardComplexLocalClass ℚ (q + 1) := by
  have hj : (q + 1) * 2 = 2 + q * 2 := by ring
  have hreal : relativeHomologyMap ℚ (2 + q * 2) (standardComplexRealPairIso (q + 1)).hom
      (relativeHomologyMap ℚ (2 + q * 2) (ccm17_intersectionPair q)
        (ccm17_shuffleHomologyClass q)) = hj ▸ standardLocalClass ℚ ((q + 1) * 2) := by
    change ((relativeHomologyMap ℚ (2 + q * 2) (standardComplexRealPairIso (q + 1)).hom).comp
      (relativeHomologyMap ℚ (2 + q * 2) (ccm17_intersectionPair q)))
        (ccm17_shuffleHomologyClass q) = _
    rw [← relativeHomologyMap_comp, ccm17_shuffleHomologyClass_eq_chainClass,
      ccm17_chainClass_map _ _ _ _ (ccm17_chainCycle_map _ _ _
        (ccm17_complexShuffleChain_relativeCycle q)),
      ← ccm17_reindexPair_standardLocalClass (2 + q * 2) ((q + 1) * 2) hj,
      ← ccm17_realShuffle_class (q * 2) (ccm17_realShuffle_punctCycle (q * 2)),
      ccm17_chainClass_map _ _ _ _ (ccm17_chainCycle_map _ _ _
        (ccm17_realShuffle_punctCycle (q * 2)))]
    apply ccm17_chainClass_congr
    rw [ccm17_complexShuffleChain_real]
  have h := ccm17_iso_homology_cast (standardComplexRealPairIso (q + 1)) hj
    (standardLocalClass ℚ ((q + 1) * 2)) _ hreal
  rw [← h]
  unfold standardComplexLocalClass
  rw [ccm17_homology_cast_trans]
  rfl

private theorem ccm17_cohomology_cast_cancel {P : TopPair.{0}} {m n : ℕ} (h h' : m = n)
    (x : RelativeCohomology ℚ P n) : h' ▸ h.symm ▸ x = x := by
  subst h
  rfl

/- Chain calculations behind the coordinate product law:
* `ccm17_normalized_complexShuffle_evaluation` evaluates the actual relative
  cup lift on `ccm17_complexShuffleChain` as 1, using representatives of the
  independently normalized factor coclasses.
* The face lemmas and `ccm17_smallShuffleFace_boundary_sum` show that the
  signed shuffle chain is a cycle of the small relative complex;
  `ccm17_shuffleHomologyClass` is its comparison class and
  `ccm17_shuffleHomologyClass_evaluation_cast` pairs the frozen cup product
  with it to 1.

Orientation comparison, independent of the cup product:
* `ccm17_chainClass` is the class of an explicit relative cycle, with
  naturality `ccm17_chainClass_map`; `ccm17_ofSubsetHomotopy` turns one
  continuous family into a homotopy of subset pairs.
* `ccm17_signedFace_boundary_sum` is the face cancellation for any face
  function killing faces that omit a vertex of either factor, and
  `ccm17_realShuffleChain_cycle` applies it to the real shuffle chain in
  `Fin (2 + n) → ℝ`.
* `ccm17_realShuffle_shift_class`: translating the head coordinates by the
  diagonal vector `ccm17_headShift n` is a homotopy of pairs from the shift
  support, so the class is unchanged.
* `ccm17_realShuffleChain_shift_projection`: after the shift, only the
  ordered shuffle simplex meets the origin (`ccm17_shiftedShuffle_ne_zero`).
* `ccm17_orderedSimplex_class`: the straight line from the shifted ordered
  simplex to `standardSingularSimplex` avoids the origin on every face
  (`ccm17_orderedLine_ne_zero`, `ccm17_orderedLine_algebra`), so the two
  classes agree through the identity simplex of the standard simplex.
* `ccm17_realShuffle_class` combines these: the signed real shuffle chain
  represents `standardLocalClass ℚ (2 + n)` with coefficient 1.
* `ccm17_complexBlock_coordinates` identifies consecutive real coordinates of
  the block map with concatenation, and `ccm17_shuffleHomologyClass_standard`
  transports the real statement to
    relativeHomologyMap ℚ (2 + q * 2) (ccm17_intersectionPair q)
      (ccm17_shuffleHomologyClass q) = _ ▸ standardComplexLocalClass ℚ (q + 1).

The target follows from this comparison, the unit pairing
`ccm17_shuffleHomologyClass_evaluation_cast`, the degree transport
`ccm17_pairing_degree_cast` and `ccm17_eq_normalized_pullback`.
-/
theorem ccm17_coordinate_product_aux (q : ℕ) :
    ccm15_relativeCup (TopCat.of (Fin (q + 1) → ℂ))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
      (ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q)) 2 (2 * q)
      (ccm17_normalClass (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q))
      (ccm17_normalClass (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q)) = ccm17_intersectionClass q := by
  have h : 2 * (q + 1) = 2 + 2 * q := by ring
  have hz : h ▸ relativeHomologyMap ℚ (2 * (q + 1)) (ccm17_intersectionPairIso q).inv
      (standardComplexLocalClass ℚ (q + 1)) =
      (congrArg (2 + ·) (Nat.mul_comm q 2)) ▸ ccm17_shuffleHomologyClass q := by
    have h1 := ccm17_iso_homology_cast (ccm17_intersectionPairIso q)
      (show 2 * (q + 1) = 2 + q * 2 by ring) (standardComplexLocalClass ℚ (q + 1))
      (ccm17_shuffleHomologyClass q) (by
        rw [ccm17_intersectionPairIso_hom]
        exact ccm17_shuffleHomologyClass_standard q)
    rw [← h1, ccm17_homology_cast_trans]
  have hev := ccm17_shuffleHomologyClass_evaluation_cast q
  dsimp only at hev
  rw [← hz, ← ccm17_pairing_degree_cast h] at hev
  have hu := ccm17_eq_normalized_pullback (q + 1) (ccm17_intersectionPairIso q) _ hev
  rw [ccm17_intersectionPairIso_hom] at hu
  unfold ccm17_intersectionClass
  rw [← hu]
  exact (ccm17_cohomology_cast_cancel h _ _).symm

theorem ccm17_relativeCup_pullback_aux (Y Z : TopCat.{0}) (f : C(Y, Z))
    (S T : Closeds Z) (p q : ℕ)
    (u : RelativeCohomology ℚ (TopPair.ofSubset (S : Set Z)ᶜ) p)
    (v : RelativeCohomology ℚ (TopPair.ofSubset (T : Set Z)ᶜ) q) :
    relativeCohomologyMap ℚ (p + q) (ccm17_preimagePair Y Z f (S ⊓ T))
      (ccm15_relativeCup Z S T p q u v) =
    ccm15_relativeCup Y (S.preimage f.continuous) (T.preimage f.continuous) p q
      (relativeCohomologyMap ℚ p (ccm17_preimagePair Y Z f S) u)
      (relativeCohomologyMap ℚ q (ccm17_preimagePair Y Z f T) v) := by
  obtain ⟨a, rfl⟩ := ((ccm17_dualEquiv
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (S : Set Z)ᶜ)) p).surjective.comp
      (ccm15_relativeDual Z S p).moduleCatHomologyClass_surjective) u
  obtain ⟨b, rfl⟩ := ((ccm17_dualEquiv
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (T : Set Z)ᶜ)) q).surjective.comp
      (ccm15_relativeDual Z T q).moduleCatHomologyClass_surjective) v
  change relativeCohomologyMap ℚ (p + q) _
    (ccm15_relativeCup Z S T p q (ccm17_dualClass _ p a) (ccm17_dualClass _ q b)) =
    ccm15_relativeCup Y (S.preimage f.continuous) (T.preimage f.continuous) p q
      (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap
        ((relativeChainFunctor ℚ).map (ccm17_preimagePair Y Z f S))) p
        (ccm17_dualClass _ p a))
      (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap
        ((relativeChainFunctor ℚ).map (ccm17_preimagePair Y Z f T))) q
        (ccm17_dualClass _ q b))
  rw [ccm17_relativeCup_class, ccm17_dualClass_naturality, ccm17_dualClass_naturality,
    ccm17_relativeCup_class]
  refine (ccm17_transport_cycle_naturality Y Z f S T (p + q)
    (ccm15_cycleCup Z S T p q a b)).trans ?_
  congr 2
  apply Subtype.ext
  exact ccm17_smallCup_pullback Y Z f S T p q a.1 b.1

#print axioms ccm17_dualClass_evaluation
#print axioms ccm17_relativeCup_evaluation
#print axioms ccm17_relativeCup_evaluation_lift
#print axioms ccm17_relativeCupLift_sum
#print axioms ccm17_smallCycle_representative
#print axioms ccm17_smallCycle_lift
#print axioms ccm17_relativeCup_pullback_aux

end HodgeLean.Adapters
