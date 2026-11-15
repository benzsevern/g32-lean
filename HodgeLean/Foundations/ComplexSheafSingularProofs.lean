import HodgeLean.Adapters.DeRhamAbelian
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CoefficientSubdivisionCochain
import HodgeLean.Foundations.SingularComparison
import HodgeLean.Foundations.ComplexSheafSingularDefs
import HodgeLean.Foundations.ComplexSheafSingularParts.EdgeMap
import HodgeLean.Foundations.ComplexSheafSingularParts.Scalar

/-! # Proofs for the complex sheaf-to-singular comparison

One proof per statement of `HodgeLean.Foundations.ComplexSheafSingular`, all closed. Statements
1–6 generalize upstream statements over `ℚ` (HodgeConjecture `2ead713`) to a coefficient ring or
field `K`, with the same shape, and are proved by ports of the upstream proofs
(`HodgeLean/Foundations/Port/AlgebraicTopology/Singular/Coefficient*.lean`). Statements 7–14 are
assembled here from them, with the edge-map bijectivity for bounded-below flasque complexes and
the scalar naturality of the named comparison proved in
`HodgeLean/Foundations/ComplexSheafSingularParts/`. The ingredients, statement by statement:

* small-chain approximation: `coverSmallRationalChainApproximation_of_openCover`
  (`Lemmas/AlgebraicTopology/Singular/Excision/Field.lean`), with `Int.castAddHom K` in place of
  `Int.castAddHom ℚ`;
* the cochain restriction: `rationalCochainRestrictionToCoverSmall_quasiIso`
  (`Lemmas/AlgebraicTopology/Singular/Sheaf/SubdivisionCochain.lean`);
* locally zero primitives and the plus comparison: `exists_topOpenLocallyZero_primitive` and
  `topOpenToGlobalSingularCochainPlusComplex_quasiIso` (same file, `section RationalCover`);
* the sheaf comparison: `topOpenToGlobalSingularCochainSheafComplex_quasiIso` (same file);
* flasqueness and the assembly: `singularCochainSheafComplexInt_isFlasque` and
  `rationalSingularCochainHypercohomologyAddEquivCohomology`
  (`HodgeLean/Foundations/Port/AlgebraicGeometry/Cohomology/GlobalSections.lean`);
* bijectivity of the edge map `globalSectionsToHypercohomology` for the singular-cochain
  resolution: termwise flasqueness, a K-injective resolution, `globalSectionsComplex_map_quasiIso`
  and `CohomologyClass.equivOfIsKInjective`, as in
  `rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution`;
* bijectivity of the named comparison `singularToFieldCohomology`
  (`HodgeLean.Foundations.ComplexSheafSingularDefs`): a short assembly of the sheaf comparison
  and the edge-map bijectivity above with the equivalence legs;
* scalar naturality of the named comparison: naturality of each leg in the scalar endomorphisms
  `c ·` of the coefficients (`fieldScalarSheaf`, `hypercohomologyAddEquivConstantCohomology_symm_smul`);
* the `K`-linear equivalence: `LinearEquiv.ofBijective` of the named comparison, made linear by its
  scalar naturality, then `LinearEquiv.symm`. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open HodgeLean.RealDefs

namespace HodgeLean.Foundations

theorem spec_coverSmallChainApproximation_of_openCover_aux (K : Type) [CommRing K]
    {ι : Type} (Y : TopCat.{0}) (U : ι → Set Y) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : ⋃ i, U i = Set.univ) :
    HomologicalComplex.homotopyEquivalences (ModuleCat K) (ComplexShape.down ℕ)
      (SSet.chainComplexMap (coverSmallSingularSubcomplex Y U).ι (ModuleCat.of K K)) := by
  exact AlgebraicTopology.Singular.coverSmallCoefficientChainApproximation_of_openCover K Y U
    hUopen hUcover

theorem spec_cochainRestrictionToCoverSmall_quasiIso_aux (K : Type) [CommRing K]
    {ι : Type} (Y : TopCat.{0}) (U : ι → Set Y) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (HomologicalComplex.linearDualMap
      (SSet.chainComplexMap (coverSmallSingularSubcomplex Y U).ι (ModuleCat.of K K))) := by
  exact AlgebraicTopology.Singular.coefficientCochainRestrictionToCoverSmall_quasiIso K Y U
    hUopen hUcover

theorem spec_exists_topOpenLocallyZero_primitive_aux (K : Type) [Field K]
    (Y : TopCat.{0}) (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : (TopOpenSingularChainComplex K Y).linearDualCochainComplex.X n)
    (hφlocal : ∀ I : S.Arrow, (singularCochainPresheaf K Y n).map I.f.op φ = 0)
    (hφclosed : ((TopOpenSingularChainComplex K Y).linearDualCochainComplex.d
      n (n + 1)) φ = 0) :
    ∃ ψ : (TopOpenSingularChainComplex K Y).linearDualCochainComplex.X
        ((ComplexShape.up ℕ).prev n),
      ((TopOpenSingularChainComplex K Y).linearDualCochainComplex.sc n).f ψ = φ ∧
        ∀ I : S.Arrow,
          (singularCochainPresheaf K Y ((ComplexShape.up ℕ).prev n)).map I.f.op ψ = 0 := by
  exact AlgebraicTopology.Singular.exists_topOpenLocallyZero_primitive_coeff K Y S n φ hφlocal
    hφclosed

theorem spec_topOpenToGlobalSingularCochainPlusComplex_quasiIso_aux (K : Type) [Field K]
    (Y : TopCat.{0}) :
    QuasiIso (topOpenToGlobalSingularCochainPlusComplex K Y) := by
  exact AlgebraicTopology.Singular.topOpenToGlobalSingularCochainPlusComplex_quasiIso_coeff K Y

theorem spec_topOpenToGlobalSingularCochainSheafComplex_quasiIso_aux (K : Type) [Field K]
    (Y : TopCat.{0}) [ParacompactSpace Y] [T2Space Y] :
    QuasiIso (topOpenToGlobalSingularCochainSheafComplex K Y) := by
  exact AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex_quasiIso_coeff K Y

theorem spec_singularCochainSheafComplexInt_isFlasque_aux (K : Type) [CommRing K]
    (X : Over (Spec ↧ℂ)) [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (n : ℤ) :
    TopCat.Sheaf.IsFlasque ((singularCochainSheafComplexInt X K).X n) := by
  by_cases hn : ∃ m : ℕ, (m : ℤ) = n
  · obtain ⟨m, rfl⟩ := hn
    let e := (AlgebraicTopology.Singular.singularCochainSheafComplex K
      (TopCat.of (ComplexPoint X))).extendXIso
        ComplexShape.embeddingUpNat (i := m) rfl
    let hP : TopCat.Presheaf.IsFlasque
        ((AlgebraicTopology.Singular.singularCochainSheafComplex K
          (TopCat.of (ComplexPoint X))).X m).obj := by
      change TopCat.Sheaf.IsFlasque
        (AlgebraicTopology.Singular.singularCochainSheaf K
          (TopCat.of (ComplexPoint X)) m)
      infer_instance
    change TopCat.Presheaf.IsFlasque
      ((singularCochainSheafComplexInt X K).X (m : ℤ)).obj
    exact @AlgebraicTopology.Singular.presheaf_isFlasque_of_iso _ _ _
      ((TopCat.Sheaf.forget AddCommGrpCat
        (TopCat.of (ComplexPoint X))).mapIso e.symm) hP
  · apply TopCat.Sheaf.IsFlasque.of_isZero
    exact (AlgebraicTopology.Singular.singularCochainSheafComplex K
      (TopCat.of (ComplexPoint X))).isZero_extend_X
        ComplexShape.embeddingUpNat n (fun i hi ↦ hn ⟨i, hi⟩)

theorem spec_singularCochainHypercohomology_addEquiv_cohomology_aux (K : Type) [Field K]
    (X : Over (Spec ↧ℂ)) [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (n : ℕ) :
    Nonempty (Hypercohomology X (singularCochainSheafComplexInt X K) (n : ℤ) ≃+
      AlgebraicTopology.Singular.Cohomology K (TopCat.of (ComplexPoint X)) n) := by
  let Y := TopCat.of (ComplexPoint X)
  have : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  have := spec_topOpenToGlobalSingularCochainSheafComplex_quasiIso_aux K Y
  exact ⟨(AddEquiv.ofBijective
      (globalSectionsToHypercohomology X (singularCochainSheafComplexInt X K) n)
      (globalSectionsToHypercohomology_bijective_of_flasque X _ 0
        (spec_singularCochainSheafComplexInt_isFlasque_aux K X) n)).symm.trans <|
    (HomologicalComplex.homologyMapIso (globalSectionsSingularCochainComplexIntIsoExtendField K X)
      (n : ℤ)).addCommGroupIsoToAddEquiv.trans <|
    ((globalSingularCochainSheafComplex K Y).extendHomologyIso ComplexShape.embeddingUpNat
      (j := n) rfl).addCommGroupIsoToAddEquiv.trans <|
    (asIso (HomologicalComplex.homologyMap (topOpenToGlobalSingularCochainSheafComplex K Y)
      n)).addCommGroupIsoToAddEquiv.symm.trans (ordinarySingularCohomologyEquivGlobalRaw K Y n).symm⟩

theorem spec_globalSectionsToHypercohomology_bijective_aux (K : Type) [CommRing K]
    (X : Over (Spec ↧ℂ)) [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (n : ℤ) :
    Function.Bijective
      (globalSectionsToHypercohomology X (singularCochainSheafComplexInt X K) n) := by
  exact globalSectionsToHypercohomology_bijective_of_flasque X _ 0
    (spec_singularCochainSheafComplexInt_isFlasque_aux K X) n

theorem spec_singularToFieldCohomology_bijective_aux (K : Type) [Field K]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (n : ℕ) :
    Function.Bijective (singularToFieldCohomology K X n) := by
  let Y := TopCat.of (ComplexPoint X)
  have : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  have := spec_topOpenToGlobalSingularCochainSheafComplex_quasiIso_aux K Y
  have hH : Function.Bijective
      (HomologicalComplex.homologyMap (topOpenToGlobalSingularCochainSheafComplex K Y) n) :=
    ConcreteCategory.bijective_of_isIso _
  exact ((hypercohomologyAddEquivConstantCohomology K X n).bijective.comp
    (fieldHypercohomologySingularCochainAddEquiv K X n).symm.bijective).comp
    ((spec_globalSectionsToHypercohomology_bijective_aux K X n).comp
      ((HomologicalComplex.homologyMapIso (globalSectionsSingularCochainComplexIntIsoExtendField K X)
          (n : ℤ)).symm.addCommGroupIsoToAddEquiv.bijective.comp
        (((globalSingularCochainSheafComplex K Y).extendHomologyIso ComplexShape.embeddingUpNat
          (j := n) rfl).symm.addCommGroupIsoToAddEquiv.bijective.comp
          (hH.comp (ordinarySingularCohomologyEquivGlobalRaw K Y n).bijective))))

theorem spec_singularToFieldCohomology_smul_aux (K : Type) [Field K]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℕ) (c : K)
    (x : AlgebraicTopology.Singular.Cohomology K (TopCat.of (ComplexPoint X)) n) :
    singularToFieldCohomology K X n (c • x) = c • singularToFieldCohomology K X n x := by
  exact singularToFieldCohomology_smul K X n c x

theorem spec_fieldCohomology_linearEquiv_singular_aux (K : Type) [Field K] [Algebra K ℂ]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U] (n : ℕ) :
    Nonempty (H^n(X; K) ≃ₗ[K]
      AlgebraicTopology.Singular.Cohomology K (TopCat.of (ComplexPoint X)) n) := by
  exact ⟨(LinearEquiv.ofBijective
    { toFun := singularToFieldCohomology K X n
      map_add' := map_add _
      map_smul' := spec_singularToFieldCohomology_smul_aux K X n }
    (spec_singularToFieldCohomology_bijective_aux K X n)).symm⟩

theorem spec_complexCohomology_linearEquiv_singular_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) :
    Nonempty (H^n(X; ℂ) ≃ₗ[ℂ]
      AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) n) := by
  have (U : Opens (ComplexPoint X)) : ParacompactSpace U := openParacompactSpace X U
  exact spec_fieldCohomology_linearEquiv_singular_aux ℂ X n

theorem spec_bettiDeRhamIso_abelian_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    BettiDeRhamIso X := by
  exact ⟨fun n ↦ HodgeLean.Adapters.spec_bijective_bettiDeRhamHQ_of_complexSingular X n
    (spec_complexCohomology_linearEquiv_singular_aux X n).some⟩

theorem spec_finrank_complexCohomology_one_abelian_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    Module.finrank ℂ H^1(X; ℂ) = 2 * dim X.left := by
  obtain ⟨e⟩ := spec_complexCohomology_linearEquiv_singular_aux X 1
  rw [e.finrank_eq, (HodgeLean.Adapters.spec_finrank_complexSingular_abelian X 1).2,
    Nat.choose_one_right]

end HodgeLean.Foundations
