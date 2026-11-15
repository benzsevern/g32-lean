import HodgeLean.Foundations.Port.AlgebraicGeometry.Cohomology.SingularComparison

/-! # The named complex sheaf-to-singular comparison

Defines `singularToFieldCohomology K X n : H^n_sing(X(ℂ); K) →+ H^n(X(ℂ); K)` for a field `K` and
smooth integral `X`, the map whose bijectivity and `K`-linearity
`HodgeLean.Foundations.ComplexSheafSingular` freezes.

The map runs from singular to sheaf cohomology because that direction inverts no open fact. Each
leg is either an upstream equivalence or a map that exists for every complex:

1. `ordinarySingularCohomologyEquivGlobalRaw`: singular cohomology is the homology of the raw
   global cochain complex;
2. the homology map of `topOpenToGlobalSingularCochainSheafComplex` (raw cochains to global
   sections of the singular-cochain sheaf complex), which is only a map here: its bijectivity is
   the open statement `spec_topOpenToGlobalSingularCochainSheafComplex_quasiIso`;
3. `extendHomologyIso` and `globalSectionsSingularCochainComplexIntIsoExtendField`, which pass to
   the integer-indexed resolution `singularCochainSheafComplexInt X K`;
4. `globalSectionsToHypercohomology`, the canonical edge map `H^n(Γ(S)) → ℍ^n(S)`, defined for
   every complex `S` by viewing a cocycle of `Hom^•(ℤ[0], S)` as a morphism in the derived
   category; its bijectivity needs flasqueness (open statement
   `spec_singularCochainSheafComplexInt_isFlasque`), its definition does not;
5. the inverse of `postcompEquiv (constantsToSingularCochainComplexInt X K)`, whose
   quasi-isomorphism hypothesis upstream proves for smooth `X`
   (`constantsToSingularCochainComplexInt_quasiIso`);
6. `hypercohomologyAddEquivConstantCohomology K X n`.

No leg chooses anything: the map is canonical. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace

namespace HodgeLean.Foundations

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Taking global sections commutes with extending the natural-number-indexed `K`-singular-cochain
sheaf complex by zero to integer degrees.

Source: upstream `Other/AlgebraicGeometry/Cohomology/GlobalSections.lean` at `2ead713`,
`ComplexPoint.globalSectionsSingularCochainComplexIntIsoExtend` (ported in this repository), with
`ℚ` replaced by a commutative ring `K`; the proof never used `ℚ`. -/
def globalSectionsSingularCochainComplexIntIsoExtendField (K : Type) [CommRing K]
    (X : Over (Spec ↧ℂ)) :
    TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X K) ≅
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex K
        (TopCat.of (ComplexPoint X))).extend
          ComplexShape.embeddingUpNat :=
  let Y := TopCat.of (ComplexPoint X)
  let F := TopCat.Sheaf.forget AddCommGrpCat Y
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)
  let G := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let S := AlgebraicTopology.Singular.singularCochainSheafComplex K Y
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : E.Additive := by dsimp [E]; infer_instance
  let eComp : F ⋙ E ≅ G := Iso.refl _
  HomologicalComplex.mapExtendCanonicalIso G S ComplexShape.embeddingUpNat ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).mapIso
      ((Functor.mapHomologicalComplexCompIso eComp (ComplexShape.up ℕ)).app S).symm

example (X : Over (Spec ↧ℂ)) :
    (globalSectionsSingularCochainComplexIntIsoExtendField ℂ X).hom ≫
        (globalSectionsSingularCochainComplexIntIsoExtendField ℂ X).inv = 𝟙 _ :=
  Iso.hom_inv_id _

section EdgeMap

local instance edgeMapHasDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- A cohomology class of `Hom^•(ℤ[0], S)` for an integer-indexed complex `S` of sheaves on `X(ℂ)`,
viewed as a hypercohomology class: a morphism `ℤ[0] → S[n]` in the homotopy category, sent to the
derived category and precomposed with `constantIntegerSheafComplexIntIsoSingle`.

Source: Mathlib's `CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom` (the localization
map from the homotopy category to the derived category), as in upstream's
`rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution`
(`Other/AlgebraicGeometry/Cohomology/GlobalSections.lean` at `2ead713`). -/
def cohomologyClassToHypercohomology (X : Over (Spec ↧ℂ))
    (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    CochainComplex.HomComplex.CohomologyClass
        (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) S n →+
      Hypercohomology X S n where
  toFun x :=
    (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
      (constantIntegerSheafComplexIntIsoSingle X).hom).comp x.toSmallShiftedHom (add_zero n)
  map_zero' := by
    apply (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    rw [hypercohomologyEquiv_zero, Localization.SmallShiftedHom.equiv_comp,
      ← CochainComplex.HomComplex.CohomologyClass.mk_zero,
      CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk]
    simp
  map_add' x y := by
    obtain ⟨a, rfl⟩ := x.mk_surjective
    obtain ⟨b, rfl⟩ := y.mk_surjective
    apply (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    rw [hypercohomologyEquiv_add, ← CochainComplex.HomComplex.CohomologyClass.mk_add]
    simp only [Localization.SmallShiftedHom.equiv_comp,
      CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk,
      map_add, ShiftedHom.map_add, ShiftedHom.comp_add]

example (X : Over (Spec ↧ℂ)) (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    cohomologyClassToHypercohomology X S n 0 = 0 :=
  map_zero _

/-- The canonical edge map `H^n(Γ(X(ℂ), S)) → ℍ^n(X(ℂ); S)` for an integer-indexed complex `S` of
sheaves of abelian groups on `X(ℂ)`: a degree-`n` cohomology class of global sections is a class of
`Hom^•(ℤ[0], S)` (`homComplexSingleIntegerIsoGlobalSections`), sent on by
`cohomologyClassToHypercohomology`. It is bijective when `S` is a bounded-below complex of flasque
sheaves; this definition assumes nothing.

Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, II.4 (the map from cohomology of global
sections to sheaf cohomology); upstream's `rationalSingularCochainHypercohomologyAddEquivGlobalSectionsOfResolution`
(`Other/AlgebraicGeometry/Cohomology/GlobalSections.lean` at `2ead713`) is its inverse for
`S = singularCochainSheafComplexInt X ℚ`, computed through an injective resolution. -/
def globalSectionsToHypercohomology (X : Over (Spec ↧ℂ))
    (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) S).homology n →+
      Hypercohomology X S n :=
  (cohomologyClassToHypercohomology X S n).comp
    ((HomologicalComplex.homologyMapIso
      (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint X)) S)
        n).symm.addCommGroupIsoToAddEquiv.trans
      (CochainComplex.HomComplex.homologyAddEquiv _ S n)).toAddMonoidHom

example (X : Over (Spec ↧ℂ)) (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ)
    (x y : (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) S).homology n) :
    globalSectionsToHypercohomology X S n (x + y) =
      globalSectionsToHypercohomology X S n x + globalSectionsToHypercohomology X S n y :=
  map_add _ x y

end EdgeMap

/-- Hypercohomology of the constant `K`-sheaf complex is additively equivalent to hypercohomology
of its singular-cochain resolution on a smooth `X`, by postcomposition with
`constantsToSingularCochainComplexInt X K`.

Source: upstream `HodgeConjecture/Lemmas/AlgebraicGeometry/Cohomology/SingularSheafComparison.lean`
at `2ead713`, `ComplexPoint.rationalHypercohomologySingularCochainAddEquiv`, with `ℚ` replaced by a
field `K`; the quasi-isomorphism is upstream's coefficient-generic
`constantsToSingularCochainComplexInt_quasiIso`. -/
def fieldHypercohomologySingularCochainAddEquiv (K : Type) [Field K] (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Hypercohomology X (constantFieldSheafComplexInt K X) n ≃+
      Hypercohomology X (singularCochainSheafComplexInt X K) n where
  toEquiv := Localization.SmallShiftedHom.postcompEquiv
    (constantsToSingularCochainComplexInt X K)
    (constantsToSingularCochainComplexInt_quasiIso X K)
  map_add' α β :=
    (hypercohomologyMap X (constantsToSingularCochainComplexInt X K) n).map_add α β

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : Hypercohomology X (constantFieldSheafComplexInt ℂ X) n) :
    (fieldHypercohomologySingularCochainAddEquiv ℂ X n).symm
        (fieldHypercohomologySingularCochainAddEquiv ℂ X n α) = α :=
  AddEquiv.symm_apply_apply _ _

/-- The named comparison `H^n_sing(X(ℂ); K) → H^n(X(ℂ); K)` from singular to constant-sheaf
cohomology, for a field `K` and smooth integral `X`: singular cohomology as homology of raw global
cochains, then global sections of the singular-cochain sheaf complex, the edge map to its
hypercohomology, the inverse of the constants-to-cochains equivalence, and Mathlib's sheaf
cohomology. It is additive by construction; its bijectivity and its `K`-linearity are frozen
statements of `HodgeLean.Foundations.ComplexSheafSingular`.

Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1 (singular cochain sheaves resolve the
constant sheaf); upstream's `rationalCohomologyAddEquivSingularCohomology`
(`Other/AlgebraicGeometry/Cohomology/GlobalSections.lean` at `2ead713`) is the same comparison
for `K = ℚ`, in the opposite direction. -/
def singularToFieldCohomology (K : Type) [Field K] (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    AlgebraicTopology.Singular.Cohomology K (TopCat.of (ComplexPoint X)) n →+ H^n(X; K) :=
  let Y := TopCat.of (ComplexPoint X)
  let G := AlgebraicTopology.Singular.globalSingularCochainSheafComplex K Y
  ((hypercohomologyAddEquivConstantCohomology K X n).toAddMonoidHom.comp
    (fieldHypercohomologySingularCochainAddEquiv K X n).symm.toAddMonoidHom).comp <|
  (globalSectionsToHypercohomology X (singularCochainSheafComplexInt X K) n).comp <|
  ((HomologicalComplex.homologyMapIso
      (globalSectionsSingularCochainComplexIntIsoExtendField K X) (n : ℤ)).symm
        |>.addCommGroupIsoToAddEquiv.toAddMonoidHom).comp <|
  ((G.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).symm
      |>.addCommGroupIsoToAddEquiv.toAddMonoidHom).comp <|
  (HomologicalComplex.homologyMap
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex K Y) n).hom.comp
    (AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw K Y n).toAddMonoidHom

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) 1 →+ H^1(X; ℂ) :=
  singularToFieldCohomology ℂ X 1

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    singularToFieldCohomology ℂ X n 0 = 0 :=
  map_zero _

end HodgeLean.Foundations
