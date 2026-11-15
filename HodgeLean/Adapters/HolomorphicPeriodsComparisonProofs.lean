import HodgeLean.Adapters.HolomorphicPeriodsComparisonDefs
import HodgeLean.Adapters.HolomorphicPeriodsCocycle
import HodgeLean.Foundations.ComplexSheafSingular

/-! # Proof obligations for `HolomorphicPeriodsComparison`

One `_aux` per statement of `HodgeLean.Adapters.HolomorphicPeriodsComparison`, all open.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped Simplicial TensorProduct Topology

namespace HodgeLean.Adapters

theorem fieldToComplexConstantSheafComplexInt_complex_eq_id (X : Over (Spec ↧ℂ)) :
    fieldToComplexConstantSheafComplexInt ℂ X = 𝟙 _ := by
  have hs : fieldToComplexConstantSheaf ℂ X = 𝟙 _ := by
    unfold fieldToComplexConstantSheaf
    rw [show (algebraMap ℂ ℂ).toAddMonoidHom = AddMonoidHom.id ℂ from rfl]
    exact (TopCat.Sheaf.constantFunctor _).map_id _
  unfold fieldToComplexConstantSheafComplexInt
  rw [hs, CategoryTheory.Functor.map_id, HomologicalComplex.extendMap_id]
  rfl

theorem fieldToDeRhamCohomology_complex_eq (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) (v : H^n(X; ℂ)) :
    fieldToDeRhamCohomology ℂ X n v =
      hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) n
        ((hypercohomologyAddEquivConstantCohomology ℂ X n).symm v) := by
  unfold fieldToDeRhamCohomology fieldToHolomorphicDeRhamComplexInt
  simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
  rw [hypercohomologyMap_comp_apply, fieldToComplexConstantSheafComplexInt_complex_eq_id,
    hypercohomologyMap_id]
  rfl

theorem spec_fieldToDeRhamCohomology_complex_bijective_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    Function.Bijective (fieldToDeRhamCohomology ℂ X n) := by
  have hi : HomologicalComplex.quasiIso _ _ (constantsToHolomorphicDeRhamComplexInt X) := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have hpost : Function.Bijective
      (hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) (n : ℤ)) :=
    (Localization.SmallShiftedHom.postcompEquiv.{1} _ hi (a := (n : ℤ))).bijective
  have : ⇑(fieldToDeRhamCohomology ℂ X n) =
      hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) n ∘
        (hypercohomologyAddEquivConstantCohomology ℂ X n).symm := by
    funext v
    exact fieldToDeRhamCohomology_complex_eq X n v
  rw [this]
  exact hpost.comp (hypercohomologyAddEquivConstantCohomology ℂ X n).symm.bijective

theorem spec_fieldToDeRhamCohomology_fieldCohomologyToComplex_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) (v : H^n(X; ℚ)) :
    fieldToDeRhamCohomology ℂ X n (fieldCohomologyToComplex X n v) =
      fieldToDeRhamCohomology ℚ X n v := by
  rw [fieldToDeRhamCohomology_complex_eq]
  unfold fieldCohomologyToComplex fieldToDeRhamCohomology fieldToHolomorphicDeRhamComplexInt
  simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
    AddEquiv.symm_apply_apply]
  rw [hypercohomologyMap_comp_apply]

theorem cochain_ext_chainOfSimplex {R : Type} [CommRing R] {Y : SSet.{0}} {n : ℕ}
    (φ ψ : AlgebraicTopology.Simplicial.Cochain R Y n)
    (h : ∀ σ : Y _⦋n⦌, φ (AlgebraicTopology.Simplicial.chainOfSimplex R σ) =
      ψ (AlgebraicTopology.Simplicial.chainOfSimplex R σ)) : φ = ψ := by
  have hc : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := by
    apply SSet.chainComplex_hom_ext
    intro σ
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    have hi : (Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a =
        a • AlgebraicTopology.Simplicial.chainOfSimplex R σ := by
      rw [AlgebraicTopology.Simplicial.chainOfSimplex, ← map_smul]
      simp
    change φ ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a) =
      ψ ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a)
    rw [hi, map_smul, map_smul, h]
  exact congrArg ModuleCat.Hom.hom hc

theorem cochainBaseChange_chainOfSimplex (Y : SSet.{0}) (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cochain ℚ Y n) (σ : Y _⦋n⦌) :
    cochainBaseChange Y n ψ (AlgebraicTopology.Simplicial.chainOfSimplex ℂ σ) =
      (ψ (AlgebraicTopology.Simplicial.chainOfSimplex ℚ σ) : ℂ) :=
  spec_simplexCochain_chainOfSimplex_aux ℂ Y n _ σ

theorem spec_coboundary_cochainBaseChange_aux (Y : SSet.{0}) (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cochain ℚ Y n) :
    AlgebraicTopology.Simplicial.coboundary ℂ n (cochainBaseChange Y n ψ) =
      cochainBaseChange Y (n + 1) (AlgebraicTopology.Simplicial.coboundary ℚ n ψ) := by
  refine cochain_ext_chainOfSimplex _ _ fun τ ↦ ?_
  rw [AlgebraicTopology.Simplicial.coboundary_chainOfSimplex, cochainBaseChange_chainOfSimplex,
    AlgebraicTopology.Simplicial.coboundary_chainOfSimplex]
  simp only [cochainBaseChange_chainOfSimplex, smul_eq_mul]
  push_cast
  rfl


section BaseChangeComparison
open AlgebraicTopology.Singular

local instance (Y : TopCat) (n : ℕ) : Module ℚ ((CChains Y).X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (Y : TopCat) (n : ℕ) : Module ℚ (CCyclesModel Y n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (Y : TopCat) (n : ℕ) : Module ℚ ((CChains Y).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

theorem cochainBaseChange_qToCChainGroup (Y : TopCat.{0}) (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj Y) n) (x : (QChains Y).X n) :
    cochainBaseChange _ n ψ (qToCChainGroup Y n x) = (ψ x : ℂ) := by
  let L₁ : (QChains Y).X n →ₗ[ℚ] ℂ :=
    { toFun := fun x ↦ cochainBaseChange _ n ψ (qToCChainGroup Y n x)
      map_add' := fun a b ↦ by simp only [map_add]
      map_smul' := fun q a ↦ by
        rw [map_smul]
        change cochainBaseChange _ n ψ ((algebraMap ℚ ℂ q) • qToCChainGroup Y n a) = _
        rw [map_smul, RingHom.id_apply, smul_eq_mul, Rat.smul_def, eq_ratCast] }
  let L₂ : (QChains Y).X n →ₗ[ℚ] ℂ := (Algebra.linearMap ℚ ℂ) ∘ₗ ψ
  have hL : L₁ = L₂ := by
    have hc : ModuleCat.ofHom (X := (QChains Y).X n) (Y := ModuleCat.of ℚ ℂ) L₁ =
        ModuleCat.ofHom (X := (QChains Y).X n) (Y := ModuleCat.of ℚ ℂ) L₂ := by
      apply SSet.chainComplex_hom_ext
      intro σ
      refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
      have hi : ((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom a =
          a • AlgebraicTopology.Simplicial.chainOfSimplex ℚ σ := by
        rw [AlgebraicTopology.Simplicial.chainOfSimplex, ← map_smul]
        simp
      change L₁ (((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom a) =
        L₂ (((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom a)
      rw [hi, map_smul, map_smul]
      congr 1
      change cochainBaseChange _ n ψ
          (qToCChainGroup Y n (AlgebraicTopology.Simplicial.chainOfSimplex ℚ σ)) = _
      rw [qToCChainGroup_chainOfSimplex, cochainBaseChange_chainOfSimplex]
      rfl
    exact congrArg ModuleCat.Hom.hom hc
  exact LinearMap.congr_fun hL x

theorem qToCChainGroup_mem_ker (Y : TopCat.{0}) (n : ℕ)
    (zq : LinearMap.ker ((QChains Y).sc n).g.hom) :
    qToCChainGroup Y n zq.1 ∈ LinearMap.ker ((CChains Y).sc n).g.hom := by
  have h1 := ConcreteCategory.congr_hom
    ((qToCChainMap Y).comm n ((ComplexShape.down ℕ).next n)) zq.1
  have h2 : ((QChains Y).sc n).g.hom zq.1 = 0 := zq.2
  change ((CChains Y).d n _).hom (qToCChainGroup Y n zq.1) = 0
  change ((CChains Y).d n _).hom (qToCChainGroup Y n zq.1) =
    qToCChainGroup Y _ (((QChains Y).d n _).hom zq.1) at h1
  have h3 : ((QChains Y).d n ((ComplexShape.down ℕ).next n)).hom zq.1 = 0 := h2
  rw [h1, h3, map_zero]

theorem spec_cohomologyBaseChange_tmul_cohomologyClass_aux (Y : TopCat.{0}) (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj Y) n)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj Y) n)
    (h : Ψ.1 = cochainBaseChange _ n ψ.1) :
    cohomologyBaseChange Y n (1 ⊗ₜ Singular.cohomologyClass Y n ψ) =
      Singular.cohomologyClass Y n Ψ := by
  apply (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ Y n).injective
  simp only [cohomologyBaseChange, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (complexHomologyEquivBaseChange Y n).surjective x
  let F := LinearMap.liftBaseChange ℂ (Module.Dual.baseChange ℂ ∘ₗ
    (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℚ Y n).toLinearMap)
      (1 ⊗ₜ[ℚ] Singular.cohomologyClass Y n ψ)
  have hF : ∀ v, F (1 ⊗ₜ v) = AlgebraicTopology.Singular.cohomologyEquivDualHomology ℚ
      Y n (Singular.cohomologyClass Y n ψ) v • (1 : ℂ) := by
    intro v
    simp only [F, LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply,
      LinearEquiv.coe_coe, Module.Dual.baseChange_apply_tmul]
  let G : (ℂ ⊗[ℚ] (AlgebraicTopology.Singular.QChains Y).homology n) →ₗ[ℂ] ℂ :=
    (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ Y n
      (Singular.cohomologyClass Y n Ψ)) ∘ₗ (complexHomologyEquivBaseChange Y n).toLinearMap
  refine (Module.Dual.congr_apply_apply (complexHomologyEquivBaseChange Y n) F _).trans ?_
  rw [LinearEquiv.symm_apply_apply]
  change F y = G y
  induction y with
  | add a b ha hb =>
    exact (F.map_add a b).trans ((congrArg₂ (· + ·) ha hb).trans (G.map_add a b).symm)
  | tmul a v =>
    have e1 : a ⊗ₜ[ℚ] v = a • ((1 : ℂ) ⊗ₜ[ℚ] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e1]
    refine (F.map_smul a _).trans ?_
    refine Eq.trans ?_ (G.map_smul a _).symm
    congr 1
    obtain ⟨zq, rfl⟩ := ShortComplex.moduleCatHomologyClass_surjective _ v
    have he : complexHomologyEquivBaseChange Y n
        ((1 : ℂ) ⊗ₜ[ℚ] ((AlgebraicTopology.Singular.SingularChainComplex ℚ Y).sc n
          ).moduleCatHomologyClass zq) =
        ((AlgebraicTopology.Singular.SingularChainComplex ℂ Y).sc n).moduleCatHomologyClass
          ⟨_, qToCChainGroup_mem_ker Y n zq⟩ := by
      refine (IsBaseChange.equiv_tmul (qToCHomology_isBaseChange Y n) 1 _).trans ?_
      refine (one_smul ℂ _).trans ?_
      exact qToCHomology_moduleCatHomologyClass _ _ zq _ rfl
    refine Eq.trans ?_ ((congrArg (AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ Y n
      (Singular.cohomologyClass Y n Ψ)) he).trans
        (cohomologyEquivDualHomology_cohomologyClass Y n Ψ _)).symm
    refine (hF _).trans ?_
    refine (congrArg (· • (1 : ℂ)) (cohomologyEquivDualHomology_cohomologyClass Y n ψ zq)).trans ?_
    change (ψ.1 zq.1) • (1 : ℂ) = Ψ.1 (qToCChainGroup Y n zq.1)
    rw [h, Rat.smul_def, mul_one]
    exact (cochainBaseChange_qToCChainGroup Y n ψ.1 zq.1).symm

end BaseChangeComparison

/-- `singularToFieldCohomology` as an explicit composite of its legs. -/
lemma singularToFieldCohomology_apply (K : Type) [Field K] (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (x : AlgebraicTopology.Singular.Cohomology K (TopCat.of (ComplexPoint X)) n) :
    singularToFieldCohomology K X n x =
      hypercohomologyAddEquivConstantCohomology K X n
        ((fieldHypercohomologySingularCochainAddEquiv K X n).symm
          (globalSectionsToHypercohomology X (singularCochainSheafComplexInt X K) n
            ((HomologicalComplex.homologyMapIso
              (globalSectionsSingularCochainComplexIntIsoExtendField K X) (n : ℤ)).inv
              ((HomologicalComplex.extendHomologyIso
                (AlgebraicTopology.Singular.globalSingularCochainSheafComplex K
                  (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat (j := n) rfl).inv
                (HomologicalComplex.homologyMap
                  (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex K
                    (TopCat.of (ComplexPoint X))) n
                  (AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw K
                    (TopCat.of (ComplexPoint X)) n x)))))) :=
  rfl

/-- Two simplicial cochains with the same values on simplices are equal. -/
theorem cochain_ext_of_simplex {R : Type} [CommRing R] {Y : SSet.{0}} {n : ℕ}
    (φ ψ : AlgebraicTopology.Simplicial.Cochain R Y n)
    (h : ∀ σ : Y _⦋n⦌, φ (AlgebraicTopology.Simplicial.chainOfSimplex R σ) =
      ψ (AlgebraicTopology.Simplicial.chainOfSimplex R σ)) : φ = ψ := by
  have hc : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := by
    apply SSet.chainComplex_hom_ext
    intro σ
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    have hi : (Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a =
        a • AlgebraicTopology.Simplicial.chainOfSimplex R σ := by
      rw [AlgebraicTopology.Simplicial.chainOfSimplex, ← map_smul]
      simp
    change φ ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a) =
      ψ ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom a)
    rw [hi, map_smul, map_smul, h]
  exact congrArg ModuleCat.Hom.hom hc

/-- `cochainBaseChange` as an additive map.
Source: Hatcher, *Algebraic Topology*, §3.1 (change of coefficients along the additive map
`ℚ → ℂ`); `cochainBaseChange`. -/
def cochainBaseChangeHom (Y : SSet.{0}) (n : ℕ) :
    AlgebraicTopology.Simplicial.Cochain ℚ Y n →+ AlgebraicTopology.Simplicial.Cochain ℂ Y n where
  toFun := cochainBaseChange Y n
  map_zero' := cochain_ext_of_simplex _ _ fun σ ↦ by
    rw [cochainBaseChange_chainOfSimplex, LinearMap.zero_apply, LinearMap.zero_apply, Rat.cast_zero]
  map_add' φ ψ := cochain_ext_of_simplex _ _ fun σ ↦ by
    rw [cochainBaseChange_chainOfSimplex, LinearMap.add_apply, LinearMap.add_apply,
      cochainBaseChange_chainOfSimplex, cochainBaseChange_chainOfSimplex, Rat.cast_add]

example (Y : SSet.{0}) (n : ℕ) (ψ : AlgebraicTopology.Simplicial.Cochain ℚ Y n) :
    cochainBaseChangeHom Y n ψ = cochainBaseChange Y n ψ := rfl

/-- Pulling back along a map of simplicial sets commutes with the base change. -/
theorem cochainBaseChange_dualMap {Y Z : SSet.{0}} (f : Y ⟶ Z) (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cochain ℚ Z n) :
    cochainBaseChange Y n (((SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f n).hom.dualMap ψ) =
      ((SSet.chainComplexMap f (ModuleCat.of ℂ ℂ)).f n).hom.dualMap (cochainBaseChange Z n ψ) :=
  cochain_ext_of_simplex _ _ fun σ ↦ by
    rw [cochainBaseChange_chainOfSimplex, LinearMap.dualMap_apply, LinearMap.dualMap_apply,
      AlgebraicTopology.Simplicial.chainOfSimplex_map,
      AlgebraicTopology.Simplicial.chainOfSimplex_map, cochainBaseChange_chainOfSimplex]

section BaseChange

variable (Y : TopCat.{0})

set_option backward.isDefEq.respectTransparency false in
/-- The base change `ℚ → ℂ` on the presheaf of singular `n`-cochains.
Source: Hatcher, *Algebraic Topology*, §3.1 (change of coefficients); `cochainBaseChange`. -/
def singularCochainPresheafBaseChange (n : ℕ) :
    AlgebraicTopology.Singular.singularCochainPresheaf ℚ Y n ⟶
      AlgebraicTopology.Singular.singularCochainPresheaf ℂ Y n where
  app U := AddCommGrpCat.ofHom (cochainBaseChangeHom _ n)
  naturality {U V} i := by
    ext φ
    exact cochainBaseChange_dualMap (TopCat.toSSet.map ((Opens.toTopCat Y).map i.unop)) n φ

example (n : ℕ) (U : (Opens Y)ᵒᵖ) (φ : AlgebraicTopology.Singular.OpenCochains ℚ Y U n) :
    (singularCochainPresheafBaseChange Y n).app U φ = cochainBaseChange _ n φ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The base change `ℚ → ℂ` on the singular-cochain presheaf complex.
Source: Hatcher, *Algebraic Topology*, §3.1 (the coboundary commutes with change of
coefficients). -/
def singularCochainPresheafComplexBaseChange :
    AlgebraicTopology.Singular.singularCochainPresheafComplex ℚ Y ⟶
      AlgebraicTopology.Singular.singularCochainPresheafComplex ℂ Y :=
  CochainComplex.ofHom (fun n ↦ singularCochainPresheafBaseChange Y n) (fun n ↦ by
    rw [AlgebraicTopology.Singular.singularCochainPresheafComplex_d,
      AlgebraicTopology.Singular.singularCochainPresheafComplex_d]
    ext U φ
    exact spec_coboundary_cochainBaseChange_aux _ n φ)

example (n : ℕ) :
    (singularCochainPresheafComplexBaseChange Y).f n = singularCochainPresheafBaseChange Y n := rfl

/-- The base change `ℚ → ℂ` on the singular-cochain sheaf complex: the sheafification of
`singularCochainPresheafComplexBaseChange`.
Source: Bredon, *Sheaf Theory*, III.1. -/
def singularCochainSheafComplexBaseChange :
    AlgebraicTopology.Singular.singularCochainSheafComplex ℚ Y ⟶
      AlgebraicTopology.Singular.singularCochainSheafComplex ℂ Y :=
  ((presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (singularCochainPresheafComplexBaseChange Y)

example (n : ℕ) :
    (singularCochainSheafComplexBaseChange Y).f n =
      (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
        (singularCochainPresheafBaseChange Y n) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Constant zero-cochains commute with the base change. -/
lemma constantsToSingularCochainZero_baseChange :
    AlgebraicTopology.Singular.constantsToSingularCochainZero ℚ Y ≫
        singularCochainPresheafBaseChange Y 0 =
      (Functor.const _).map (AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom) ≫
        AlgebraicTopology.Singular.constantsToSingularCochainZero ℂ Y := by
  ext U r
  change ℚ at r
  refine cochain_ext_of_simplex _ _ fun σ ↦ ?_
  change cochainBaseChange _ 0 (r • (AlgebraicTopology.Singular.openZeroAugmentation ℚ Y (op U)).hom)
      (AlgebraicTopology.Simplicial.chainOfSimplex ℂ σ) =
    ((algebraMap ℚ ℂ r) • (AlgebraicTopology.Singular.openZeroAugmentation ℂ Y (op U)).hom)
      (AlgebraicTopology.Simplicial.chainOfSimplex ℂ σ)
  have hK : ∀ (K : Type) [CommRing K], (AlgebraicTopology.Singular.openZeroAugmentation K Y (op U)).hom
      (AlgebraicTopology.Simplicial.chainOfSimplex K σ) = 1 := fun K _ ↦
    ConcreteCategory.congr_hom
      (AlgebraicTopology.Singular.ιChainComplex_comp_simplicialZeroAugmentation K _ σ) (1 : K)
  rw [cochainBaseChange_chainOfSimplex, LinearMap.smul_apply, LinearMap.smul_apply]
  erw [hK, hK]
  simp

/-- The sheafified constant zero-cochains commute with the base change. -/
lemma constantsToSingularCochainSheafComplex_baseChange :
    AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex ℚ Y ≫
        singularCochainSheafComplexBaseChange Y =
      (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat Y)).map
          ((TopCat.Sheaf.constantFunctor Y).map
            (AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom)) ≫
        AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex ℂ Y := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f,
    AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex]
  change _ ≫ (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
      (AlgebraicTopology.Singular.constantsToSingularCochainZero ℚ Y) ≫
      (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
        (singularCochainPresheafBaseChange Y 0) = _ ≫
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
      ((Functor.const _).map (AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom)) ≫
      (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
        (AlgebraicTopology.Singular.constantsToSingularCochainZero ℂ Y)
  rw [← Functor.map_comp, ← Functor.map_comp, constantsToSingularCochainZero_baseChange]
  rfl

/-- The base change `ℚ → ℂ` on the integer-indexed singular-cochain sheaf complex.
Source: Bredon, *Sheaf Theory*, III.1. -/
def singularCochainSheafComplexIntBaseChange (X : Over (Spec ↧ℂ)) :
    singularCochainSheafComplexInt X ℚ ⟶ singularCochainSheafComplexInt X ℂ :=
  HomologicalComplex.extendMap
    (singularCochainSheafComplexBaseChange (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat

example (X : Over (Spec ↧ℂ)) :
    singularCochainSheafComplexIntBaseChange X = HomologicalComplex.extendMap
      (singularCochainSheafComplexBaseChange (TopCat.of (ComplexPoint X)))
      ComplexShape.embeddingUpNat := rfl

/-- The constants-to-cochains maps intertwine the inclusion of constants `ℚ → ℂ` with the base
change. -/
lemma constantsToSingularCochainComplexInt_baseChange (X : Over (Spec ↧ℂ)) :
    constantsToSingularCochainComplexInt X ℚ ≫ singularCochainSheafComplexIntBaseChange X =
      fieldToComplexConstantSheafComplexInt ℚ X ≫ constantsToSingularCochainComplexInt X ℂ := by
  have := congrArg (fun φ ↦ HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
    (constantsToSingularCochainSheafComplex_baseChange (TopCat.of (ComplexPoint X)))
  simp only [HomologicalComplex.extendMap_comp] at this
  exact this

/-- The inverse of the constants-to-cochains equivalences intertwines the base change with the
inclusion of constants. -/
lemma fieldHypercohomologySingularCochainAddEquiv_symm_baseChange (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (z : Hypercohomology X (singularCochainSheafComplexInt X ℚ) n) :
    (fieldHypercohomologySingularCochainAddEquiv ℂ X n).symm
        (hypercohomologyMap X (singularCochainSheafComplexIntBaseChange X) n z) =
      hypercohomologyMap X (fieldToComplexConstantSheafComplexInt ℚ X) n
        ((fieldHypercohomologySingularCochainAddEquiv ℚ X n).symm z) := by
  rw [AddEquiv.symm_apply_eq]
  obtain ⟨y, rfl⟩ := (fieldHypercohomologySingularCochainAddEquiv ℚ X n).surjective z
  rw [AddEquiv.symm_apply_apply]
  change hypercohomologyMap X _ n (hypercohomologyMap X (constantsToSingularCochainComplexInt X ℚ) n y) =
    hypercohomologyMap X (constantsToSingularCochainComplexInt X ℂ) n
      (hypercohomologyMap X (fieldToComplexConstantSheafComplexInt ℚ X) n y)
  have h1 := hypercohomologyMap_comp_apply X (constantsToSingularCochainComplexInt X ℚ)
    (singularCochainSheafComplexIntBaseChange X) n y
  have h2 := hypercohomologyMap_comp_apply X (fieldToComplexConstantSheafComplexInt ℚ X)
    (constantsToSingularCochainComplexInt X ℂ) n y
  rw [constantsToSingularCochainComplexInt_baseChange] at h1
  exact h1.symm.trans h2

/-- The base change `ℚ → ℂ` on raw global singular cochains.
Source: Hatcher, *Algebraic Topology*, §3.1. -/
def globalRawSingularCochainComplexBaseChange :
    AlgebraicTopology.Singular.globalRawSingularCochainComplex ℚ Y ⟶
      AlgebraicTopology.Singular.globalRawSingularCochainComplex ℂ Y :=
  (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (singularCochainPresheafComplexBaseChange Y)

example (n : ℕ) :
    (globalRawSingularCochainComplexBaseChange Y).f n =
      (singularCochainPresheafBaseChange Y n).app (.op ⊤) := rfl

/-- The base change `ℚ → ℂ` on global sections of the singular-cochain sheaf complex.
Source: Bredon, *Sheaf Theory*, III.1. -/
def globalSingularCochainSheafComplexBaseChange :
    AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ Y ⟶
      AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ Y :=
  (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      (((TopCat.Sheaf.forget AddCommGrpCat Y).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (singularCochainSheafComplexBaseChange Y))

example (n : ℕ) :
    (globalSingularCochainSheafComplexBaseChange Y).f n =
      ((singularCochainSheafComplexBaseChange Y).f n).hom.app (.op ⊤) := rfl

/-- The comparison from raw cochains to global sections of the sheaf complex commutes with the
base change. -/
lemma topOpenToGlobalSingularCochainSheafComplex_baseChange :
    AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℚ Y ≫
        globalSingularCochainSheafComplexBaseChange Y =
      globalRawSingularCochainComplexBaseChange Y ≫
        AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℂ Y := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex_f,
    AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex_f]
  exact congrArg (fun f ↦ f.app (.op ⊤))
    (toSheafify_naturality (Opens.grothendieckTopology Y) (singularCochainPresheafBaseChange Y n)).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Taking global sections commutes with extension by zero, compatibly with the base change. -/
lemma globalSectionsSingularCochainComplexIntIsoExtendField_baseChange (X : Over (Spec ↧ℂ)) :
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map
          (singularCochainSheafComplexIntBaseChange X) ≫
        (globalSectionsSingularCochainComplexIntIsoExtendField ℂ X).hom =
      (globalSectionsSingularCochainComplexIntIsoExtendField ℚ X).hom ≫
        HomologicalComplex.extendMap
          (globalSingularCochainSheafComplexBaseChange (TopCat.of (ComplexPoint X)))
          ComplexShape.embeddingUpNat := by
  dsimp only [globalSectionsSingularCochainComplexIntIsoExtendField,
    singularCochainSheafComplexIntBaseChange, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, HomologicalComplex.mapExtendCanonicalIso_naturality, Category.assoc,
    Category.assoc]
  congr 1
  change HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _ =
    HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  congr 1

attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData

set_option backward.isDefEq.respectTransparency false in
/-- A singular cohomology class is the homology class of a cycle of the singular cochain complex
whose underlying cochain is the given cocycle. -/
theorem exists_cohomologyClass_eq_homologyπ (K : Type) [Field K] (n : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cocycle K (TopCat.toSSet.obj Y) n) :
    ∃ c : (AlgebraicTopology.Singular.SingularCochainComplex K Y).cycles n,
      ((AlgebraicTopology.Singular.SingularCochainComplex K Y).iCycles n).hom c = φ.1 ∧
      Singular.cohomologyClass Y n φ =
        ((AlgebraicTopology.Singular.SingularCochainComplex K Y).homologyπ n).hom c := by
  let L := AlgebraicTopology.Singular.SingularChainComplex K Y
  let e := HomologicalComplex.linearDualCochainComplexScIso L n
  have hφ : ((L.sc n).linearDual.g).hom φ.1 = 0 := by
    change ((L.sc n).f.hom.dualMap) φ.1 = 0
    have hψ : AlgebraicTopology.Simplicial.coboundary K n φ.1 = 0 := φ.2
    change (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of K K)).d
      ((ComplexShape.down ℕ).prev n) n).hom.dualMap φ.1 = 0
    rw [ChainComplex.prev]
    exact hψ
  let x : LinearMap.ker (L.sc n).linearDual.g.hom := ⟨φ.1, hφ⟩
  let a := (L.sc n).linearDual.moduleCatCyclesIso.inv.hom x
  refine ⟨(ShortComplex.cyclesMap e.inv).hom a, ?_, ?_⟩
  · have hc := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i e.inv) a
    change ((AlgebraicTopology.Singular.SingularCochainComplex K Y).sc n).iCycles.hom
      ((ShortComplex.cyclesMap e.inv).hom a) = e.inv.τ₂.hom ((L.sc n).linearDual.iCycles.hom a) at hc
    refine hc.trans ?_
    have hs : (L.sc n).linearDual.iCycles.hom a = x.1 :=
      ConcreteCategory.congr_hom (L.sc n).linearDual.moduleCatCyclesIso_inv_iCycles x
    rw [hs]
    rfl
  · have h1 : Singular.cohomologyClass Y n φ =
        (ShortComplex.homologyMap e.inv).hom
          ((L.sc n).linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk x)) := rfl
    have ha : (L.sc n).linearDual.homologyπ.hom a =
        (L.sc n).linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk x) :=
      ConcreteCategory.congr_hom (L.sc n).linearDual.moduleCatCyclesIso_inv_π x
    rw [h1, ← ha]
    exact ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality e.inv) a

set_option backward.isDefEq.respectTransparency false in
/-- The raw comparison sends the class of a singular cocycle to the class of the corresponding
top-open cochain. -/
theorem ordinarySingularCohomologyEquivGlobalRaw_homologyπ (K : Type) [CommRing K] (n : ℕ)
    (c : (AlgebraicTopology.Singular.SingularCochainComplex K Y).cycles n) :
    ∃ c' : (AlgebraicTopology.Singular.globalRawSingularCochainComplex K Y).cycles n,
      (AlgebraicTopology.Singular.globalRawSingularCochainComplex K Y).iCycles n c' =
        ((AlgebraicTopology.Singular.singularCochainComplexIsoTopOpen K Y).hom.f n).hom
          (((AlgebraicTopology.Singular.SingularCochainComplex K Y).iCycles n).hom c) ∧
      AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw K Y n
          (((AlgebraicTopology.Singular.SingularCochainComplex K Y).homologyπ n).hom c) =
        (AlgebraicTopology.Singular.globalRawSingularCochainComplex K Y).homologyπ n c' := by
  let i := AlgebraicTopology.Singular.singularCochainComplexIsoTopOpen K Y
  let T := (AlgebraicTopology.Singular.TopOpenSingularChainComplex K Y).linearDualCochainComplex
  let F := forget₂ (ModuleCat K) AddCommGrpCat
  let G := AlgebraicTopology.Singular.globalRawSingularCochainComplexIso K Y
  let d := (HomologicalComplex.cyclesMap i.hom n).hom c
  let mC := (T.sc n).mapCyclesIso F
  let e : (AlgebraicTopology.Singular.topOpenForgottenSingularCochainComplex K Y).cycles n :=
    mC.inv d
  refine ⟨HomologicalComplex.cyclesMap G.inv n e, ?_, ?_⟩
  · rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
    have h1 : (AlgebraicTopology.Singular.topOpenForgottenSingularCochainComplex K Y).iCycles n e =
        F.map (T.iCycles n) (mC.hom e) := by
      rw [← ConcreteCategory.comp_apply]
      exact (ConcreteCategory.congr_hom (ShortComplex.mapCyclesIso_hom_iCycles (T.sc n) F) e).symm
    rw [h1]
    change (T.iCycles n).hom (mC.hom (mC.inv d)) = _
    rw [Iso.inv_hom_id_apply]
    exact ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i i.hom n) c
  · rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply]
    change HomologicalComplex.homologyMap G.inv n
        ((AlgebraicTopology.Singular.topOpenForgottenSingularCochainHomologyIso K Y n).inv
          (F.map (HomologicalComplex.homologyMap i.hom n)
            (((AlgebraicTopology.Singular.SingularCochainComplex K Y).homologyπ n).hom c))) = _
    congr 1
    have h2 : F.map (HomologicalComplex.homologyMap i.hom n)
        (((AlgebraicTopology.Singular.SingularCochainComplex K Y).homologyπ n).hom c) =
        F.map (T.homologyπ n) d :=
      ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality i.hom n) c
    have h3 : ((T.sc n).mapHomologyIso F).hom (((T.sc n).map F).homologyπ e) =
        F.map (T.homologyπ n) d := by
      have := ConcreteCategory.congr_hom (HodgeLean.RealDefs.homologyπ_mapHomologyIso_hom (T.sc n) F) e
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
      rw [this]
      change F.map (T.homologyπ n) (mC.hom (mC.inv d)) = _
      rw [Iso.inv_hom_id_apply]
    rw [h2, ← h3]
    exact Iso.hom_inv_id_apply _ _

set_option backward.isDefEq.respectTransparency false in
/-- The raw comparison is natural for the base change of cocycles. -/
theorem ordinarySingularCohomologyEquivGlobalRaw_baseChange (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj Y) n)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj Y) n)
    (h : Ψ.1 = cochainBaseChange _ n ψ.1) :
    AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw ℂ Y n
        (Singular.cohomologyClass Y n Ψ) =
      HomologicalComplex.homologyMap (globalRawSingularCochainComplexBaseChange Y) n
        (AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw ℚ Y n
          (Singular.cohomologyClass Y n ψ)) := by
  obtain ⟨a, ha1, ha2⟩ := exists_cohomologyClass_eq_homologyπ Y ℚ n ψ
  obtain ⟨b, hb1, hb2⟩ := exists_cohomologyClass_eq_homologyπ Y ℂ n Ψ
  obtain ⟨a', ha1', ha2'⟩ := ordinarySingularCohomologyEquivGlobalRaw_homologyπ Y ℚ n a
  obtain ⟨b', hb1', hb2'⟩ := ordinarySingularCohomologyEquivGlobalRaw_homologyπ Y ℂ n b
  rw [ha2, hb2, ha2', hb2', ← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]
  congr 1
  apply ConcreteCategory.injective_of_mono_of_preservesPullback
    ((AlgebraicTopology.Singular.globalRawSingularCochainComplex ℂ Y).iCycles n)
  rw [hb1', hb1, h, ← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
    ConcreteCategory.comp_apply, ha1', ha1]
  exact (cochainBaseChange_dualMap (TopCat.toSSet.map (Opens.inclusionTopIso Y).hom) n ψ.1).symm

end BaseChange

/-- A square through two isomorphisms, inverted. -/
lemma inv_comp_eq_of_comp_hom' {C : Type*} [Category* C] {A B A' B' : C} (i : A ≅ B) (i' : A' ≅ B')
    {a : A ⟶ A'} {b : B ⟶ B'} (h : a ≫ i'.hom = i.hom ≫ b) : i.inv ≫ a = b ≫ i'.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The sheaf-side legs of statement 5: the edge map, the constants-to-cochains equivalences and
upstream's identification with sheaf cohomology commute with the base change. -/
theorem singularToFieldCohomology_baseChange_tail (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (t : (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
      (singularCochainSheafComplexInt X ℚ)).homology n) :
    hypercohomologyAddEquivConstantCohomology ℂ X n
        ((fieldHypercohomologySingularCochainAddEquiv ℂ X n).symm
          (globalSectionsToHypercohomology X (singularCochainSheafComplexInt X ℂ) n
            (HomologicalComplex.homologyMap
              (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
                (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map
                  (singularCochainSheafComplexIntBaseChange X)) n t))) =
      fieldCohomologyToComplex X n
        (hypercohomologyAddEquivConstantCohomology ℚ X n
          ((fieldHypercohomologySingularCochainAddEquiv ℚ X n).symm
            (globalSectionsToHypercohomology X (singularCochainSheafComplexInt X ℚ) n t))) := by
  rw [globalSectionsToHypercohomology_naturality,
    fieldHypercohomologySingularCochainAddEquiv_symm_baseChange]
  change _ = hypercohomologyAddEquivConstantCohomology ℂ X n
    (hypercohomologyMap X (fieldToComplexConstantSheafComplexInt ℚ X) n
      ((hypercohomologyAddEquivConstantCohomology ℚ X n).symm
        (hypercohomologyAddEquivConstantCohomology ℚ X n _)))
  rw [AddEquiv.symm_apply_apply]

theorem spec_singularToFieldCohomology_cochainBaseChange_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) n)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) n)
    (h : Ψ.1 = cochainBaseChange _ n ψ.1) :
    singularToFieldCohomology ℂ X n (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) n Ψ) =
      fieldCohomologyToComplex X n
        (singularToFieldCohomology ℚ X n
          (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) n ψ)) := by
  let Y := TopCat.of (ComplexPoint X)
  have hj : ∀ w, (HomologicalComplex.extendHomologyIso
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ Y)
        ComplexShape.embeddingUpNat (j := n) rfl).inv
      (HomologicalComplex.homologyMap (globalSingularCochainSheafComplexBaseChange Y) n w) =
      HomologicalComplex.homologyMap (HomologicalComplex.extendMap
        (globalSingularCochainSheafComplexBaseChange Y) ComplexShape.embeddingUpNat) n
        ((HomologicalComplex.extendHomologyIso
          (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ Y)
            ComplexShape.embeddingUpNat (j := n) rfl).inv w) := by
    intro w
    have h := HomologicalComplex.extendHomologyIso_hom_naturality
      (globalSingularCochainSheafComplexBaseChange Y) ComplexShape.embeddingUpNat (j := n) rfl
    rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq] at h
    exact (ConcreteCategory.congr_hom h w).symm
  have hiE := inv_comp_eq_of_comp_hom'
    (HomologicalComplex.homologyMapIso (globalSectionsSingularCochainComplexIntIsoExtendField ℚ X)
      (n : ℤ))
    (HomologicalComplex.homologyMapIso (globalSectionsSingularCochainComplexIntIsoExtendField ℂ X)
      (n : ℤ))
    (a := HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
        ℤᵘᵖ).map (singularCochainSheafComplexIntBaseChange X)) n)
    (b := HomologicalComplex.homologyMap (HomologicalComplex.extendMap
        (globalSingularCochainSheafComplexBaseChange Y) ComplexShape.embeddingUpNat) n) (by
      rw [HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_hom,
        ← HomologicalComplex.homologyMap_comp]
      erw [← HomologicalComplex.homologyMap_comp]
      rw [globalSectionsSingularCochainComplexIntIsoExtendField_baseChange]
      rfl)
  rw [singularToFieldCohomology_apply, singularToFieldCohomology_apply,
    ordinarySingularCohomologyEquivGlobalRaw_baseChange Y n ψ Ψ h,
    homologyMap_apply_of_comm' (topOpenToGlobalSingularCochainSheafComplex_baseChange Y).symm, hj]
  erw [← ConcreteCategory.congr_hom hiE, ConcreteCategory.comp_apply,
    singularToFieldCohomology_baseChange_tail]

/-- Undoing an isomorphism of abelian groups and an additive equivalence. -/
lemma addCommGroupIso_symm_trans_apply {A B : AddCommGrpCat.{0}} {C : Type*} [AddCommGroup C]
    (i : B ≅ A) (e : B ≃+ C) (c : C) :
    (i.symm.addCommGroupIsoToAddEquiv.trans e) (i.hom (e.symm c)) = c := by
  rw [AddEquiv.trans_apply, Iso.addCommGroupIsoToAddEquiv_apply, Iso.symm_hom, Iso.hom_inv_id_apply,
    AddEquiv.apply_symm_apply]

/-- The edge map inverts upstream's comparison of hypercohomology with global sections, computed
through any K-injective resolution. -/
theorem globalSectionsToHypercohomology_ofResolution (X : Over (Spec ↧ℂ))
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [I.IsKInjective]
    (i : singularCochainSheafComplexInt X ℚ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map i)]
    (n : ℤ) (α : RationalSingularCochainHypercohomology X n) :
    globalSectionsToHypercohomology X (singularCochainSheafComplexInt X ℚ) n
      (rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution X I i n α) = α := by
  let Γ := (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ
  have hi : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X) ℤᵘᵖ i := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  apply (Localization.SmallShiftedHom.postcompEquiv.{1} i hi (a := n)).injective
  change hypercohomologyMap X i n _ = hypercohomologyMap X i n α
  rw [← globalSectionsToHypercohomology_naturality]
  dsimp only [rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution,
    AddEquiv.trans_apply]
  erw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
  have key : ∀ c, globalSectionsToHypercohomology X I n
      ((HomologicalComplex.homologyMapIso
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X)) I) n).hom
          ((CochainComplex.HomComplex.homologyAddEquiv
            (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) I n).symm c)) =
        cohomologyClassToHypercohomology X I n c := by
    intro c
    dsimp only [globalSectionsToHypercohomology]
    erw [AddMonoidHom.comp_apply]
    congr 1
    erw [AddEquiv.coe_toAddMonoidHom]
    exact addCommGroupIso_symm_trans_apply _ _ c
  erw [CategoryTheory.id_apply]
  erw [key]
  change (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
      (constantIntegerSheafComplexIntIsoSingle X).hom).comp
        (CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective
          (CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.symm _)) (add_zero n) = _
  rw [Equiv.apply_symm_apply]
  change (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
      (constantIntegerSheafComplexIntIsoSingle X).hom).comp
      ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        (constantIntegerSheafComplexIntIsoSingle X).inv).comp
        (α.comp (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl i)
          (zero_add n)) (add_zero n)) (add_zero n) = α.comp
          (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl i) (zero_add n)
  rw [← Localization.SmallShiftedHom.comp_assoc _ _ _ _ _ _ (by simp),
    ← smallShiftedHomMkZero_comp, Iso.hom_inv_id, Localization.SmallShiftedHom.mk₀_id_comp]
  simp

/-- The raw comparison followed by the map to global sections undoes upstream's comparison. -/
lemma homologyMap_topOpen_ordinarySingularCohomologyEquivGlobalRaw_symm (Y : TopCat.{0})
    [ParacompactSpace Y] [T2Space Y] (n : ℕ)
    (t : (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ Y).homology n) :
    HomologicalComplex.homologyMap
        (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℚ Y) n
      (AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw ℚ Y n
        ((AlgebraicTopology.Singular.HereditarilyParacompact.ordinaryRationalSingularCohomologyEquivGlobalSections
          Y n).symm t)) = t :=
  (AlgebraicTopology.Singular.HereditarilyParacompact.ordinaryRationalSingularCohomologyEquivGlobalSections
    Y n).apply_symm_apply t

/-- Undoing an isomorphism of abelian groups applied as an equivalence. -/
lemma iso_inv_addCommGroupIsoToAddEquiv_toEquiv_apply {A B : AddCommGrpCat.{0}} (i : A ≅ B)
    (x : A) : i.inv (i.addCommGroupIsoToAddEquiv.toEquiv x) = x :=
  i.hom_inv_id_apply x

/-- For `K = ℚ` the field version of the extension isomorphism is upstream's. -/
lemma globalSectionsSingularCochainComplexIntIsoExtendField_rat (X : Over (Spec ↧ℂ)) :
    globalSectionsSingularCochainComplexIntIsoExtendField ℚ X =
      globalSectionsSingularCochainComplexIntIsoExtend X :=
  rfl

/-- For `K = ℚ` the constants-to-cochains equivalence is upstream's. -/
lemma fieldHypercohomologySingularCochainAddEquiv_rat (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    fieldHypercohomologySingularCochainAddEquiv ℚ X n =
      rationalHypercohomologySingularCochainAddEquiv X n :=
  rfl

/-- Stage 3c's rational comparison is a left inverse of upstream's. -/
theorem singularToFieldCohomology_rationalCohomologyAddEquivSingularCohomology
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (n : ℕ) (w : H^n(X; ℚ)) :
    singularToFieldCohomology ℚ X n (rationalCohomologyAddEquivSingularCohomology X n w) = w := by
  simp only [rationalCohomologyAddEquivSingularCohomology,
    rationalSingularCochainHypercohomologyAddEquivCohomology,
    rationalSingularCochainHypercohomologyAddEquivGlobalSections, AddEquiv.trans_apply]
  rw [singularToFieldCohomology_apply]
  dsimp only [AddEquiv.trans_apply]
  let : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  erw [homologyMap_topOpen_ordinarySingularCohomologyEquivGlobalRaw_symm]
  erw [iso_inv_addCommGroupIsoToAddEquiv_toEquiv_apply]
  rw [globalSectionsSingularCochainComplexIntIsoExtendField_rat]
  erw [iso_inv_addCommGroupIsoToAddEquiv_toEquiv_apply]
  rw [globalSectionsToHypercohomology_ofResolution, fieldHypercohomologySingularCochainAddEquiv_rat,
    rationalCohomologySingularCochainAddEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply,
    AddEquiv.apply_symm_apply]

set_option maxRecDepth 4000 in
/-- Stage 3c's rational comparison is a left inverse of U1. -/
theorem singularToFieldCohomology_rationalCohomologyLinearEquivSingular (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) (w : H^n(X; ℚ)) :
    singularToFieldCohomology ℚ X n (Foundations.rationalCohomologyLinearEquivSingular X n w) = w := by
  let (U : Opens (ComplexPoint X)) : ParacompactSpace U := openParacompactSpace X U
  exact singularToFieldCohomology_rationalCohomologyAddEquivSingularCohomology X n w

/-- `cupComparison` is a nonzero rational multiple of upstream's comparison, the same multiple in
every degree. -/
theorem exists_cupComparison_eq_smul (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∃ r : ℚ, r ≠ 0 ∧ ∀ (n : ℕ) (v : HQ X n), cupComparison X n v =
      r • Foundations.rationalCohomologyLinearEquivSingular X n (HQ.linearEquiv X n v) := by
  have key : ∃ r : ℚ, ∀ (n : ℕ) (v : HQ X n), cupComparison X n v =
      r • Foundations.rationalCohomologyLinearEquivSingular X n (HQ.linearEquiv X n v) := by
    let := Foundations.pathConnectedSpace_complexPoint X
    exact ⟨_, fun n v ↦ rfl⟩
  obtain ⟨r, hr⟩ := key
  refine ⟨r, fun h ↦ ?_, hr⟩
  have h0 := cupComparison_unit X
  rw [hr, h, zero_smul] at h0
  have := Foundations.pathConnectedSpace_complexPoint X
  exact Foundations.Singular.unit_ne_zero (R := ℚ) _ h0.symm

theorem spec_singularToFieldCohomology_cupComparison_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    ∃ q : ℚ, q ≠ 0 ∧ ∀ v : HQ X n,
      singularToFieldCohomology ℚ X n (cupComparison X n v) = q • HQ.linearEquiv X n v := by
  obtain ⟨r, hr, h⟩ := exists_cupComparison_eq_smul X
  refine ⟨r, hr, fun v ↦ ?_⟩
  rw [h, map_rat_smul, singularToFieldCohomology_rationalCohomologyLinearEquivSingular]

/-- The base change of the zero cochain is zero. -/
theorem cochainBaseChange_zero (Y : SSet.{0}) (n : ℕ) : cochainBaseChange Y n 0 = 0 :=
  cochain_ext_of_simplex _ _ fun σ ↦ by
    rw [cochainBaseChange_chainOfSimplex, LinearMap.zero_apply, LinearMap.zero_apply, Rat.cast_zero]

/-- The base change of a rational cocycle, as a complex cocycle (it is closed by statement 3).
Source: Hatcher, *Algebraic Topology*, §3.1 (change of coefficients on cocycles). -/
def cocycleBaseChange (Y : SSet.{0}) (n : ℕ) (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ Y n) :
    AlgebraicTopology.Simplicial.Cocycle ℂ Y n :=
  ⟨cochainBaseChange Y n ψ.1, by
    rw [LinearMap.mem_ker, spec_coboundary_cochainBaseChange_aux, LinearMap.mem_ker.mp ψ.2,
      cochainBaseChange_zero]⟩

example (Y : SSet.{0}) (n : ℕ) (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ Y n) :
    (cocycleBaseChange Y n ψ).1 = cochainBaseChange Y n ψ.1 := rfl

/-- The rational de Rham comparison commutes with rational scalars on `HQ X n`. -/
theorem fieldToDeRhamCohomology_rat_smul_linearEquiv (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) (q : ℚ) (v : HQ X n) :
    fieldToDeRhamCohomology ℚ X n (q • HQ.linearEquiv X n v) =
      (q : ℂ) • fieldToDeRhamCohomology ℚ X n v := by
  rw [Rat.cast_smul_eq_qsmul]
  exact fieldToDeRhamCohomology_smul ℚ X n q _

/-- The complex comparison of the base change of a rational class is the rational comparison, read
in de Rham cohomology (statements 2, 4 and 5). -/
theorem fieldToDeRham_singularToFieldCohomology_cohomologyBaseChange_one_tmul
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) n) :
    fieldToDeRhamCohomology ℂ X n (singularToFieldCohomology ℂ X n
        (cohomologyBaseChange (TopCat.of (ComplexPoint X)) n
          (1 ⊗ₜ Singular.cohomologyClass (TopCat.of (ComplexPoint X)) n ψ))) =
      fieldToDeRhamCohomology ℚ X n (singularToFieldCohomology ℚ X n
        (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) n ψ)) := by
  rw [spec_cohomologyBaseChange_tmul_cohomologyClass_aux _ n ψ (cocycleBaseChange _ n ψ) rfl,
    spec_singularToFieldCohomology_cochainBaseChange_aux X n ψ (cocycleBaseChange _ n ψ) rfl,
    spec_fieldToDeRhamCohomology_fieldCohomologyToComplex_aux]

/-- Statement 7 on a pure tensor. -/
theorem fieldToDeRham_singularToFieldCohomology_cohomologyBaseChange_tmul
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ)
    (q : ℚ) (h6 : ∀ v : HQ X n,
      singularToFieldCohomology ℚ X n (cupComparison X n v) = q • HQ.linearEquiv X n v)
    (a : ℂ) (v : HQ X n) :
    fieldToDeRhamCohomology ℂ X n (singularToFieldCohomology ℂ X n
        (cohomologyBaseChange (TopCat.of (ComplexPoint X)) n (a ⊗ₜ cupComparison X n v))) =
      (q : ℂ) • a • fieldToDeRhamCohomology ℚ X n v := by
  obtain ⟨ψ, hψ⟩ := Singular.cohomologyClass_surjective _ n (cupComparison X n v)
  have hab : a ⊗ₜ[ℚ] cupComparison X n v = a • (1 ⊗ₜ[ℚ] cupComparison X n v) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hab, map_smul, singularToFieldCohomology_smul, fieldToDeRhamCohomology_smul, ← hψ,
    fieldToDeRham_singularToFieldCohomology_cohomologyBaseChange_one_tmul, hψ, h6,
    fieldToDeRhamCohomology_rat_smul_linearEquiv, smul_comm]

theorem spec_deRham_singularToFieldCohomology_cohomologyBaseChange_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    ∃ q : ℚ, q ≠ 0 ∧ ∀ ω : ℂ ⊗[ℚ] HQ X n,
      fieldToDeRhamCohomology ℂ X n (singularToFieldCohomology ℂ X n
          (cohomologyBaseChange (TopCat.of (ComplexPoint X)) n
            (LinearMap.baseChange ℂ (cupComparison X n).toLinearMap ω))) =
        (q : ℂ) • bettiDeRhamHQ X n ω := by
  obtain ⟨q, hq, h6⟩ := spec_singularToFieldCohomology_cupComparison_aux X n
  refine ⟨q, hq, fun ω ↦ ?_⟩
  induction ω using TensorProduct.inductionOn with
  | tmul a v =>
    rw [LinearMap.baseChange_tmul, bettiDeRhamHQ_tmul, LinearEquiv.coe_toLinearMap,
      fieldToDeRham_singularToFieldCohomology_cohomologyBaseChange_tmul X n q h6 a v]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

theorem spec_exists_local_integration_primitive_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (x : ComplexPoint X) :
    ∃ (U : Set (ComplexPoint X)) (s : ComplexPoint X → Fin d → ℂ),
      IsOpen U ∧ x ∈ U ∧ ContinuousOn s U ∧
        (∀ y ∈ U, (complexExponential X d (s y)).toMul = y) ∧
        ∀ σ : (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) _⦋1⦌,
          (∀ t, simplexPath σ t ∈ U) →
            singularIntegrationCochain X d θ (AlgebraicTopology.Simplicial.chainOfSimplex ℂ σ) =
              expPullback X d θ 0 (s (simplexPath σ 1)) -
                expPullback X d θ 0 (s (simplexPath σ 0)) := by
  obtain ⟨v, hv⟩ := surjective_complexExponential X d (Additive.ofMul x)
  obtain ⟨e, hve, he⟩ := (spec_isCoveringMap_complexExponential X d).isLocalHomeomorph v
  have hsec : ∀ y ∈ e.target, (complexExponential X d (e.symm y)).toMul = y := by
    intro y hy
    have := congrFun he (e.symm y)
    rw [this]
    exact e.right_inv hy
  refine ⟨e.target, e.symm, e.open_target, ?_, e.continuousOn_symm, hsec, ?_⟩
  · have := congrFun he v
    have hx : x = (complexExponential X d v).toMul := by rw [hv]; rfl
    rw [hx, this]
    exact e.map_source hve
  · intro σ hσ
    let Γ : C(unitInterval, Fin d → ℂ) :=
      ⟨fun t ↦ e.symm (simplexPath σ t),
        e.continuousOn_symm.comp_continuous (simplexPath σ).continuous hσ⟩
    have hΓ : IsExpLift X d (simplexPath σ) Γ := fun t ↦ hsec _ (hσ t)
    refine (spec_simplexCochain_chainOfSimplex ℂ _ 1 _ σ).trans ?_
    rw [holomorphicPathIntegral,
      spec_expLiftDisplacement_eq X d _ Γ hΓ, map_sub]
    rfl

open scoped CategoryTheory.MonObj in
theorem spec_eventually_sub_eq_of_complexExponential_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (U U' : Set (ComplexPoint X)) (s s' : ComplexPoint X → Fin d → ℂ)
    (hU : IsOpen U) (hU' : IsOpen U') (hs : ContinuousOn s U) (hs' : ContinuousOn s' U')
    (he : ∀ y ∈ U, (complexExponential X d (s y)).toMul = y)
    (he' : ∀ y ∈ U', (complexExponential X d (s' y)).toMul = y)
    (y : ComplexPoint X) (hy : y ∈ U ∩ U') :
    ∀ᶠ y' in 𝓝 y, s y' - s' y' = s y - s' y := by
  have hmem : ∀ y' ∈ U ∩ U', s y' - s' y' ∈ complexExponentialLattice X d := by
    intro y' hy'
    change complexExponentialHom X d (s y' - s' y') = 0
    rw [map_sub]
    change complexExponential X d (s y') - complexExponential X d (s' y') = 0
    have h1 := he y' hy'.1
    have h2 := he' y' hy'.2
    rw [sub_eq_zero]
    exact congrArg Additive.ofMul (h1.trans h2.symm)
  have hopen : IsOpen ({0} : Set (complexExponentialLattice X d)) := isOpen_discrete _
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp hopen
  have hV0 : (0 : Fin d → ℂ) ∈ V := by
    have : (0 : complexExponentialLattice X d) ∈ Subtype.val ⁻¹' V := by rw [hVeq]; rfl
    exact this
  have hcont : ContinuousAt (fun y' ↦ (s y' - s' y') - (s y - s' y)) y := by
    have h1 : ContinuousAt s y := hs.continuousAt (hU.mem_nhds hy.1)
    have h2 : ContinuousAt s' y := hs'.continuousAt (hU'.mem_nhds hy.2)
    exact (h1.sub h2).sub continuousAt_const
  have hev : ∀ᶠ y' in 𝓝 y, (s y' - s' y') - (s y - s' y) ∈ V :=
    hcont.preimage_mem_nhds (by rw [sub_self]; exact hV.mem_nhds hV0)
  filter_upwards [hev, (hU.inter hU').mem_nhds hy] with y' hy'V hy'U
  have hL : (s y' - s' y') - (s y - s' y) ∈ complexExponentialLattice X d :=
    sub_mem (hmem y' hy'U) (hmem y hy)
  have : (⟨_, hL⟩ : complexExponentialLattice X d) ∈ Subtype.val ⁻¹' V := hy'V
  rw [hVeq] at this
  exact sub_eq_zero.mp (congrArg Subtype.val this)

/-- The complex comparison `G = fieldToDeRhamCohomology ℂ X n ∘ singularToFieldCohomology ℂ X n`
commutes with complex scalars. -/
private theorem complexComparison_smul (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) (a : ℂ)
    (x : AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) n) :
    fieldToDeRhamCohomology ℂ X n (singularToFieldCohomology ℂ X n (a • x)) =
      a • fieldToDeRhamCohomology ℂ X n (singularToFieldCohomology ℂ X n x) := by
  rw [spec_singularToFieldCohomology_smul, fieldToDeRhamCohomology_smul]

theorem spec_hsing_of_deRham_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (c' : ℂ) (hc' : c' ≠ 0)
    (hderham : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
        (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
          (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1),
      Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) →
        fieldToDeRhamCohomology ℂ X 1 (singularToFieldCohomology ℂ X 1
            (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ)) =
          c' • cycleDeRhamClass X z) :
    ∃ c : ℂ, ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z →
        ∀ Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
            (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1,
          Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) →
            cohomologyBaseChange (TopCat.of (ComplexPoint X)) 1
                (LinearMap.baseChange ℂ (cupComparison X 1).toLinearMap ω) =
              c • Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ := by
  have (U : Opens (ComplexPoint X)) : ParacompactSpace U := openParacompactSpace X U
  obtain ⟨q, -, hq⟩ := spec_deRham_singularToFieldCohomology_cohomologyBaseChange_aux X 1
  refine ⟨(q : ℂ) / c', fun z ω hω Ψ hΨ ↦ ?_⟩
  apply (spec_singularToFieldCohomology_bijective ℂ X 1).injective
  apply (spec_fieldToDeRhamCohomology_complex_bijective_aux X 1).injective
  rw [hq, hω, complexComparison_smul, hderham z Ψ hΨ, smul_smul,
    div_mul_cancel₀ _ hc']

theorem spec_deRham_of_hsing_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (c : ℂ) (hc : c ≠ 0)
    (hsing : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z →
        ∀ Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
            (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1,
          Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) →
            cohomologyBaseChange (TopCat.of (ComplexPoint X)) 1
                (LinearMap.baseChange ℂ (cupComparison X 1).toLinearMap ω) =
              c • Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ) :
    ∃ c' : ℂ, c' ≠ 0 ∧ ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
        (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
          (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1),
      Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) →
        fieldToDeRhamCohomology ℂ X 1 (singularToFieldCohomology ℂ X 1
            (Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ)) =
          c' • cycleDeRhamClass X z := by
  obtain ⟨q, hq0, hq⟩ := spec_deRham_singularToFieldCohomology_cohomologyBaseChange_aux X 1
  refine ⟨(q : ℂ) / c, div_ne_zero (Rat.cast_ne_zero.mpr hq0) hc, fun z Ψ hΨ ↦ ?_⟩
  obtain ⟨ω, hω⟩ := ((spec_bettiDeRhamIso_abelian X).bijective 1).surjective (cycleDeRhamClass X z)
  have h := hq ω
  rw [hsing z ω hω Ψ hΨ, complexComparison_smul, hω] at h
  rw [div_eq_inv_mul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ hc, one_smul]

end HodgeLean.Adapters
