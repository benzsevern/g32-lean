import HodgeLean.Adapters.CycleClassDivisorProduct3Construction

/-! # Absolute compatibility proof obligation
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Adapters

private def ccm15_dualEquiv (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :=
  (ShortComplex.homologyMapIso
    (HomologicalComplex.linearDualCochainComplexScIso K n)).toLinearEquiv.symm

private def ccm15_dualClass (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :=
  (ccm15_dualEquiv K n).toLinearMap.comp (K.sc n).linearDual.moduleCatHomologyClass

private theorem ccm15_dualClass_naturality
    {K L : ChainComplex (ModuleCat ℚ) ℕ} (f : K ⟶ L) (n : ℕ)
    (u : LinearMap.ker (L.sc n).linearDual.g.hom) :
    HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap f) n
        (ccm15_dualClass L n u) =
      ccm15_dualClass K n (ShortComplex.moduleCatCycleMap
        (ShortComplex.linearDualMap
          ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) n).map f)) u) := by
  apply (ccm15_dualEquiv K n).symm.injective
  have h := congrArg (ShortComplex.homologyFunctor (ModuleCat ℚ)).map
    (HomologicalComplex.linearDualCochainComplexScIso_naturality f n)
  rw [Functor.map_comp, Functor.map_comp] at h
  have hh := ConcreteCategory.congr_hom h (ccm15_dualClass L n u)
  change (ccm15_dualEquiv K n).symm
      (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap f) n
        (ccm15_dualClass L n u)) =
    (ShortComplex.homologyMap (ShortComplex.linearDualMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) n).map f))).hom
      ((ccm15_dualEquiv L n).symm
      (ccm15_dualClass L n u)) at hh
  rw [hh]
  simp only [ccm15_dualClass, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]
  exact ShortComplex.moduleCatHomologyClass_naturality _ u

private theorem ccm15_forget_transport (Y : TopCat.{0}) (S T : Closeds Y)
    (n : ℕ) (w : (ccm15_smallDual Y S T n).homology) :
    relativeCohomologyToAbsolute ℚ (TopPair.ofSubset ((S : Set Y) ∩ T)ᶜ) n
      (ccm15_dualTransport Y S T S.isClosed T.isClosed n w) =
    HomologicalComplex.homologyMap
      (HomologicalComplex.linearDualMap (ccm14_smallProjection Y S T)) n
      (ccm15_dualEquiv (ccm14_smallRelativeComplex Y S T) n w) := by
  letI := ccm15_dualComparison_quasiIso_aux Y S T S.isClosed T.isClosed
  have hf : ccm14_smallProjection Y S T ≫ ccm14_relativeComparison Y S T =
      relativeChainProjection ℚ (TopPair.ofSubset ((S : Set Y) ∩ T)ᶜ) :=
    CategoryTheory.Limits.cokernel.π_desc _ _ _
  unfold relativeCohomologyToAbsolute
  rw [← hf, HomologicalComplex.linearDualMap_comp,
    HomologicalComplex.homologyMap_comp]
  change (HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap (ccm14_smallProjection Y S T)) n).hom
      ((asIso (HomologicalComplex.homologyMap
        (HomologicalComplex.linearDualMap (ccm14_relativeComparison Y S T)) n)).toLinearEquiv
        ((asIso (HomologicalComplex.homologyMap
          (HomologicalComplex.linearDualMap (ccm14_relativeComparison Y S T)) n)).toLinearEquiv.symm
          (ccm15_dualEquiv (ccm14_smallRelativeComplex Y S T) n w))) = _
  rw [LinearEquiv.apply_symm_apply]

private theorem ccm15_absolute_cycle_cup (Y : TopCat.{0}) (p q : ℕ)
    (a : LinearMap.ker ((SingularChainComplex ℚ Y).sc p).linearDual.g.hom)
    (b : LinearMap.ker ((SingularChainComplex ℚ Y).sc q).linearDual.g.hom)
    (w : LinearMap.ker ((SingularChainComplex ℚ Y).sc (p + q)).linearDual.g.hom)
    (hw : w.1 = HodgeLean.Foundations.Singular.cupCochain Y p q a.1 b.1) :
    HodgeLean.Foundations.Singular.cup Y rfl
      (ccm15_dualClass (SingularChainComplex ℚ Y) p a)
      (ccm15_dualClass (SingularChainComplex ℚ Y) q b) =
    ccm15_dualClass (SingularChainComplex ℚ Y) (p + q) w := by
  unfold HodgeLean.Foundations.Singular.cup
  dsimp only
  simp only [ccm15_dualClass, ShortComplex.moduleCatHomologyClass,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
  erw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  erw [LinearMap.liftQ₂_mk]
  apply congrArg (ccm15_dualClass (SingularChainComplex ℚ Y) (p + q))
  apply Subtype.ext
  exact hw.symm

private theorem ccm15_relativeCup_class (Y : TopCat.{0}) (S T : Closeds Y) (p q : ℕ)
    (u : LinearMap.ker (ccm15_relativeDual Y S p).g.hom)
    (v : LinearMap.ker (ccm15_relativeDual Y T q).g.hom) :
    ccm15_relativeCup Y S T p q
      (ccm15_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (S : Set Y)ᶜ)) p u)
      (ccm15_dualClass ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (T : Set Y)ᶜ)) q v) =
    ccm15_dualTransport Y S T S.isClosed T.isClosed (p + q)
      ((ccm15_smallDual Y S T (p + q)).moduleCatHomologyClass
        (ccm15_cycleCup Y S T p q u v)) := by
  change ccm15_dualTransport Y S T S.isClosed T.isClosed (p + q)
    ((ccm15_smallDual Y S T (p + q)).moduleCatHomologyIso.inv.hom
      (ccm15_quotientCup Y S T p q
        ((ccm15_relativeDual Y S p).moduleCatHomologyIso.hom.hom
          ((ccm15_dualEquiv _ p).symm (ccm15_dualClass _ p u)))
        ((ccm15_relativeDual Y T q).moduleCatHomologyIso.hom.hom
          ((ccm15_dualEquiv _ q).symm (ccm15_dualClass _ q v))))) = _
  simp only [ccm15_dualClass, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
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

theorem ccm15_relativeCup_absolute_aux (Y : TopCat.{0}) (S T : Closeds Y) (p q : ℕ)
    (u : RelativeCohomology ℚ (TopPair.ofSubset (S : Set Y)ᶜ) p)
    (v : RelativeCohomology ℚ (TopPair.ofSubset (T : Set Y)ᶜ) q) :
    relativeCohomologyToAbsolute ℚ
      (TopPair.ofSubset ((S ⊓ T : Closeds Y) : Set Y)ᶜ) (p + q)
        (ccm15_relativeCup Y S T p q u v) =
      HodgeLean.Foundations.Singular.cup Y rfl
        (relativeCohomologyToAbsolute ℚ (TopPair.ofSubset (S : Set Y)ᶜ) p u)
        (relativeCohomologyToAbsolute ℚ (TopPair.ofSubset (T : Set Y)ᶜ) q v) := by
  obtain ⟨a, rfl⟩ := ((ccm15_dualEquiv
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (S : Set Y)ᶜ)) p).surjective.comp
      (ccm15_relativeDual Y S p).moduleCatHomologyClass_surjective) u
  obtain ⟨b, rfl⟩ := ((ccm15_dualEquiv
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (T : Set Y)ᶜ)) q).surjective.comp
      (ccm15_relativeDual Y T q).moduleCatHomologyClass_surjective) v
  change relativeCohomologyToAbsolute ℚ _ (p + q)
    (ccm15_relativeCup Y S T p q (ccm15_dualClass _ p a) (ccm15_dualClass _ q b)) = _
  rw [ccm15_relativeCup_class]
  erw [ccm15_forget_transport Y S T]
  change HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap (ccm14_smallProjection Y S T)) (p + q)
    (ccm15_dualClass _ (p + q) (ccm15_cycleCup Y S T p q a b)) =
    HodgeLean.Foundations.Singular.cup Y rfl
      (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap
        (relativeChainProjection ℚ (TopPair.ofSubset (S : Set Y)ᶜ))) p
        (ccm15_dualClass _ p a))
      (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap
        (relativeChainProjection ℚ (TopPair.ofSubset (T : Set Y)ᶜ))) q
        (ccm15_dualClass _ q b))
  rw [ccm15_dualClass_naturality, ccm15_dualClass_naturality,
    ccm15_dualClass_naturality]
  symm
  apply ccm15_absolute_cycle_cup
  exact ccm15_smallCup_projection Y S T p q a.1 b.1

end HodgeLean.Adapters
