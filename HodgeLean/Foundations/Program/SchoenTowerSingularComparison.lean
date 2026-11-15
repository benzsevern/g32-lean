import HodgeLean.Foundations.ComplexSheafSingularProofs
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainResolution

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

theorem s2v_constantsToSingularInt_quasiIso_of_contractible_basis
    (X : Over (Spec ↧ℂ))
    (hX : ∀ (x : ComplexPoint X) (U : Opens (ComplexPoint X)), x ∈ U →
      ∃ V : Opens (ComplexPoint X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (R : Type) [CommRing R] :
    QuasiIso (constantsToSingularCochainComplexInt X R) := by
  exact (HomologicalComplex.quasiIso_extendMap_iff
    (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex R
      (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat).mpr
    (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis
      R (X := TopCat.of (ComplexPoint X)) hX)

def s2v_constantSingularHypercohomologyEquiv
    (X : Over (Spec ↧ℂ))
    (hX : ∀ (x : ComplexPoint X) (U : Opens (ComplexPoint X)), x ∈ U →
      ∃ V : Opens (ComplexPoint X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℤ) :
    Hypercohomology X (constantFieldSheafComplexInt ℂ X) n ≃+
      Hypercohomology X (singularCochainSheafComplexInt X ℂ) n where
  toEquiv := Localization.SmallShiftedHom.postcompEquiv
    (constantsToSingularCochainComplexInt X ℂ)
    (s2v_constantsToSingularInt_quasiIso_of_contractible_basis X hX ℂ)
  map_add' α β :=
    (hypercohomologyMap X (constantsToSingularCochainComplexInt X ℂ) n).map_add α β

def s2v_singularToConstantCohomology
    (X : Over (Spec ↧ℂ))
    (hX : ∀ (x : ComplexPoint X) (U : Opens (ComplexPoint X)), x ∈ U →
      ∃ V : Opens (ComplexPoint X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℕ) :
    AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) n →+
      Sheaf.H ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℂ)) n :=
  let Y := TopCat.of (ComplexPoint X)
  let G := AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ Y
  ((hypercohomologyAddEquivConstantCohomology ℂ X n).toAddMonoidHom.comp
    (s2v_constantSingularHypercohomologyEquiv X hX n).symm.toAddMonoidHom).comp <|
  (globalSectionsToHypercohomology X (singularCochainSheafComplexInt X ℂ) n).comp <|
  ((HomologicalComplex.homologyMapIso
      (globalSectionsSingularCochainComplexIntIsoExtendField ℂ X) (n : ℤ)).symm
        |>.addCommGroupIsoToAddEquiv.toAddMonoidHom).comp <|
  ((G.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).symm
      |>.addCommGroupIsoToAddEquiv.toAddMonoidHom).comp <|
  (HomologicalComplex.homologyMap
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℂ Y) n).hom.comp
    (AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw ℂ Y n).toAddMonoidHom

theorem s2v_singularToConstantCohomology_bijective
    (X : Over (Spec ↧ℂ))
    (hX : ∀ (x : ComplexPoint X) (U : Opens (ComplexPoint X)), x ∈ U →
      ∃ V : Opens (ComplexPoint X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    [T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) : Function.Bijective (s2v_singularToConstantCohomology X hX n) := by
  let Y := TopCat.of (ComplexPoint X)
  have : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  have := spec_topOpenToGlobalSingularCochainSheafComplex_quasiIso_aux ℂ Y
  have hH : Function.Bijective
      (HomologicalComplex.homologyMap
        (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℂ Y) n) :=
    ConcreteCategory.bijective_of_isIso _
  exact ((hypercohomologyAddEquivConstantCohomology ℂ X n).bijective.comp
    (s2v_constantSingularHypercohomologyEquiv X hX n).symm.bijective).comp
    ((spec_globalSectionsToHypercohomology_bijective_aux ℂ X n).comp
      ((HomologicalComplex.homologyMapIso (globalSectionsSingularCochainComplexIntIsoExtendField ℂ X)
          (n : ℤ)).symm.addCommGroupIsoToAddEquiv.bijective.comp
        (((AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ Y).extendHomologyIso
            ComplexShape.embeddingUpNat (j := n) rfl).symm.addCommGroupIsoToAddEquiv.bijective.comp
          (hH.comp (AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw ℂ Y n).bijective))))

theorem s2v_constantSingularHypercohomologyEquiv_symm_scalar
    (X : Over (Spec ↧ℂ))
    (hX : ∀ (x : ComplexPoint X) (U : Opens (ComplexPoint X)), x ∈ U →
      ∃ V : Opens (ComplexPoint X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℤ) (z : ℂ) (v : Hypercohomology X (singularCochainSheafComplexInt X ℂ) n) :
    (s2v_constantSingularHypercohomologyEquiv X hX n).symm
        (hypercohomologyMap X (singularCochainSheafComplexIntScalar ℂ X z) n v) =
      hypercohomologyMap X (fieldScalarComplex ℂ X z) n
        ((s2v_constantSingularHypercohomologyEquiv X hX n).symm v) := by
  rw [AddEquiv.symm_apply_eq]
  obtain ⟨y, rfl⟩ := (s2v_constantSingularHypercohomologyEquiv X hX n).surjective v
  rw [AddEquiv.symm_apply_apply]
  change hypercohomologyMap X _ n
      (hypercohomologyMap X (constantsToSingularCochainComplexInt X ℂ) n y) =
    hypercohomologyMap X (constantsToSingularCochainComplexInt X ℂ) n
      (hypercohomologyMap X (fieldScalarComplex ℂ X z) n y)
  have h1 := hypercohomologyMap_comp_apply X (constantsToSingularCochainComplexInt X ℂ)
    (singularCochainSheafComplexIntScalar ℂ X z) n y
  have h2 := hypercohomologyMap_comp_apply X (fieldScalarComplex ℂ X z)
    (constantsToSingularCochainComplexInt X ℂ) n y
  rw [constantsToSingularCochainComplexInt_scalar] at h1
  exact h1.symm.trans h2

theorem s2v_singularToConstantCohomology_scalar
    (X : Over (Spec ↧ℂ))
    (hX : ∀ (x : ComplexPoint X) (U : Opens (ComplexPoint X)), x ∈ U →
      ∃ V : Opens (ComplexPoint X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℕ) (z : ℂ)
    (v : AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) n) :
    s2v_singularToConstantCohomology X hX n (z • v) =
      Sheaf.H.map (fieldScalarSheaf ℂ X z) n (s2v_singularToConstantCohomology X hX n v) := by
  let G := globalSingularCochainSheafComplex ℂ (TopCat.of (ComplexPoint X))
  let iE := globalSectionsSingularCochainComplexIntIsoExtendField ℂ X
  let jE := G.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl
  have hj : ∀ w, jE.inv
      (HomologicalComplex.homologyMap (globalSingularCochainSheafComplexScalar ℂ
        (TopCat.of (ComplexPoint X)) z) n w) =
      HomologicalComplex.homologyMap (HomologicalComplex.extendMap
        (globalSingularCochainSheafComplexScalar ℂ (TopCat.of (ComplexPoint X)) z)
        ComplexShape.embeddingUpNat) n (jE.inv w) := by
    intro w
    have h := HomologicalComplex.extendHomologyIso_hom_naturality
      (globalSingularCochainSheafComplexScalar ℂ (TopCat.of (ComplexPoint X)) z)
      ComplexShape.embeddingUpNat (j := n) rfl
    rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq] at h
    exact (ConcreteCategory.congr_hom h w).symm
  have hiE := inv_comp_eq_of_comp_hom iE
    (globalSectionsSingularCochainComplexIntIsoExtendField_scalar ℂ X z)
  change hypercohomologyAddEquivConstantCohomology ℂ X n
      ((s2v_constantSingularHypercohomologyEquiv X hX n).symm
        (globalSectionsToHypercohomology X (singularCochainSheafComplexInt X ℂ) n
          (HomologicalComplex.homologyMap iE.inv n (jE.inv
            (HomologicalComplex.homologyMap (topOpenToGlobalSingularCochainSheafComplex ℂ
              (TopCat.of (ComplexPoint X))) n
              (ordinarySingularCohomologyEquivGlobalRaw ℂ (TopCat.of (ComplexPoint X)) n (z • v))))))) =
    Sheaf.H.map (fieldScalarSheaf ℂ X z) n
      (hypercohomologyAddEquivConstantCohomology ℂ X n
        ((s2v_constantSingularHypercohomologyEquiv X hX n).symm
          (globalSectionsToHypercohomology X (singularCochainSheafComplexInt X ℂ) n
            (HomologicalComplex.homologyMap iE.inv n (jE.inv
              (HomologicalComplex.homologyMap (topOpenToGlobalSingularCochainSheafComplex ℂ
                (TopCat.of (ComplexPoint X))) n
                (ordinarySingularCohomologyEquivGlobalRaw ℂ (TopCat.of (ComplexPoint X)) n v)))))))
  rw [ordinarySingularCohomologyEquivGlobalRaw_smul,
    homologyMap_apply_of_comm' (topOpenToGlobalSingularCochainSheafComplex_scalar ℂ
      (TopCat.of (ComplexPoint X)) z).symm, hj]
  erw [← homologyMap_apply_of_comm' hiE, globalSectionsToHypercohomology_naturality]
  rw [s2v_constantSingularHypercohomologyEquiv_symm_scalar]
  exact hypercohomologyAddEquivConstantCohomology_map ℂ X (fieldScalarSheaf ℂ X z) n _

theorem s2v_singularConstant_equiv_with_coefficients
    (X : Over (Spec ↧ℂ))
    (hX : ∀ (x : ComplexPoint X) (U : Opens (ComplexPoint X)), x ∈ U →
      ∃ V : Opens (ComplexPoint X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    [T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    ∃ c : AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) n ≃+
        Sheaf.H ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
          (AddCommGrpCat.of ℂ)) n,
      ∀ (z : ℂ) v, c (z • v) = Sheaf.H.map (fieldScalarSheaf ℂ X z) n (c v) := by
  refine ⟨AddEquiv.ofBijective (s2v_singularToConstantCohomology X hX n)
    (s2v_singularToConstantCohomology_bijective X hX n), ?_⟩
  intro z v
  exact s2v_singularToConstantCohomology_scalar X hX n z v

end HodgeLean.Foundations.Program
