import HodgeLean.Foundations.ComplexSheafSingularParts.EdgeMap
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.GlobalRestriction
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # Scalar naturality of the named comparison

For a scalar `c : K`, the endomorphism `φ ↦ c • φ` of the singular-cochain presheaf complex, its
sheafification and its extension to integer degrees; each leg of `singularToFieldCohomology`
commutes with these endomorphisms. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular

namespace HodgeLean.Foundations

section Presheaf

variable (K : Type) [CommRing K] (Y : TopCat.{0})

/-- Multiplication by `c : K` on the presheaf of singular `n`-cochains.

Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1 (the singular-cochain presheaf is a
presheaf of `K`-modules). -/
def singularCochainPresheafScalar (c : K) (n : ℕ) :
    singularCochainPresheaf K Y n ⟶ singularCochainPresheaf K Y n where
  app U := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom _ c)
  naturality {U V} i := by
    ext φ
    apply LinearMap.ext
    intro x
    rfl

example (n : ℕ) (U : (Opens Y)ᵒᵖ) (φ : OpenCochains ℂ Y U n) :
    (singularCochainPresheafScalar ℂ Y Complex.I n).app U φ = Complex.I • φ :=
  rfl

/-- Multiplication by `c : K` on the singular-cochain presheaf complex.

Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1 (the coboundary is `K`-linear). -/
def singularCochainPresheafComplexScalar (c : K) :
    singularCochainPresheafComplex K Y ⟶ singularCochainPresheafComplex K Y :=
  CochainComplex.ofHom (fun n ↦ singularCochainPresheafScalar K Y c n) (fun n ↦ by
    rw [singularCochainPresheafComplex_d]
    ext U φ
    apply LinearMap.ext
    intro x
    rfl)

example (n : ℕ) :
    (singularCochainPresheafComplexScalar ℂ Y Complex.I).f n =
      singularCochainPresheafScalar ℂ Y Complex.I n :=
  rfl

/-- Multiplication by `c : K` on the singular-cochain sheaf complex: the sheafification of
`singularCochainPresheafComplexScalar`.

Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1. -/
def singularCochainSheafComplexScalar (c : K) :
    singularCochainSheafComplex K Y ⟶ singularCochainSheafComplex K Y :=
  ((presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (singularCochainPresheafComplexScalar K Y c)

example (n : ℕ) :
    (singularCochainSheafComplexScalar ℂ Y Complex.I).f n =
      (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
        (singularCochainPresheafScalar ℂ Y Complex.I n) :=
  rfl

/-- Constant zero-cochains commute with multiplication by `c`. -/
lemma constantsToSingularCochainZero_scalar (c : K) :
    constantsToSingularCochainZero K Y ≫ singularCochainPresheafScalar K Y c 0 =
      (Functor.const _).map (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft c)) ≫
        constantsToSingularCochainZero K Y := by
  ext U r
  apply LinearMap.ext
  intro x
  exact (mul_assoc c _ _).symm

/-- The sheafified constant zero-cochains commute with multiplication by `c`. -/
lemma constantsToSingularCochainSheafComplex_scalar (c : K) :
    constantsToSingularCochainSheafComplex K Y ≫ singularCochainSheafComplexScalar K Y c =
      (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat Y)).map
          ((TopCat.Sheaf.constantFunctor Y).map (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft c))) ≫
        constantsToSingularCochainSheafComplex K Y := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, constantsToSingularCochainSheafComplex]
  change _ ≫ (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
      (constantsToSingularCochainZero K Y) ≫
      (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
        (singularCochainPresheafScalar K Y c 0) = _ ≫
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
      ((Functor.const _).map (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft c))) ≫
      (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
        (constantsToSingularCochainZero K Y)
  rw [← Functor.map_comp, ← Functor.map_comp, constantsToSingularCochainZero_scalar]
  rfl

/-- Multiplication by `c : K` on raw global singular cochains.

Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1. -/
def globalRawSingularCochainComplexScalar (c : K) :
    globalRawSingularCochainComplex K Y ⟶ globalRawSingularCochainComplex K Y :=
  (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (singularCochainPresheafComplexScalar K Y c)

example (n : ℕ) :
    (globalRawSingularCochainComplexScalar ℂ Y Complex.I).f n =
      (singularCochainPresheafScalar ℂ Y Complex.I n).app (.op ⊤) :=
  rfl

/-- Multiplication by `c : K` on global sections of the singular-cochain sheaf complex.

Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1. -/
def globalSingularCochainSheafComplexScalar (c : K) :
    globalSingularCochainSheafComplex K Y ⟶ globalSingularCochainSheafComplex K Y :=
  (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      (((TopCat.Sheaf.forget AddCommGrpCat Y).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (singularCochainSheafComplexScalar K Y c))

example (n : ℕ) :
    (globalSingularCochainSheafComplexScalar ℂ Y Complex.I).f n =
      ((singularCochainSheafComplexScalar ℂ Y Complex.I).f n).hom.app (.op ⊤) :=
  rfl

/-- The comparison from raw cochains to global sections of the sheaf complex commutes with
multiplication by `c`. -/
lemma topOpenToGlobalSingularCochainSheafComplex_scalar (c : K) :
    topOpenToGlobalSingularCochainSheafComplex K Y ≫ globalSingularCochainSheafComplexScalar K Y c =
      globalRawSingularCochainComplexScalar K Y c ≫ topOpenToGlobalSingularCochainSheafComplex K Y := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    topOpenToGlobalSingularCochainSheafComplex_f]
  exact congrArg (fun f ↦ f.app (.op ⊤))
    (toSheafify_naturality (Opens.grothendieckTopology Y) (singularCochainPresheafScalar K Y c n)).symm

/-- A commutative square of complexes of abelian groups gives a commutative square in homology. -/
lemma homologyMap_comp_of_comm {A B C D : CochainComplex AddCommGrpCat ℕ}
    {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D} (h : a ≫ b = c ≫ d) (n : ℕ) :
    HomologicalComplex.homologyMap a n ≫ HomologicalComplex.homologyMap b n =
      HomologicalComplex.homologyMap c n ≫ HomologicalComplex.homologyMap d n := by
  rw [← HomologicalComplex.homologyMap_comp, h, HomologicalComplex.homologyMap_comp]

/-- Multiplication by a scalar on a complex of modules induces multiplication by that scalar on
homology. -/
lemma homologyMap_smul_id (T : CochainComplex (ModuleCat K) ℕ) (c : K) (n : ℕ) :
    HomologicalComplex.homologyMap (c • 𝟙 T) n = c • 𝟙 _ := by
  change ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ n).map (c • 𝟙 T)) = _
  rw [show (HomologicalComplex.shortComplexFunctor _ _ n).map (c • 𝟙 T) =
      c • 𝟙 ((HomologicalComplex.shortComplexFunctor _ _ n).obj T) by
    ext <;> rfl, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

/-- Forgetting the scalars of top-open cochains commutes with homology maps. -/
lemma topOpenForgottenSingularCochainHomologyIso_inv_naturality (n : ℕ)
    (φ : (TopOpenSingularChainComplex K Y).linearDualCochainComplex ⟶
      (TopOpenSingularChainComplex K Y).linearDualCochainComplex) :
    (forget₂ (ModuleCat K) AddCommGrpCat).map (HomologicalComplex.homologyMap φ n) ≫
      (topOpenForgottenSingularCochainHomologyIso K Y n).inv =
    (topOpenForgottenSingularCochainHomologyIso K Y n).inv ≫ HomologicalComplex.homologyMap
      (((forget₂ (ModuleCat K) AddCommGrpCat).mapHomologicalComplex _).map φ) n :=
  ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) (forget₂ (ModuleCat K) AddCommGrpCat)

/-- The raw comparison carries the module structure of singular cohomology to multiplication by
`c` on raw cochains. -/
lemma ordinarySingularCohomologyEquivGlobalRaw_smul (c : K) (n : ℕ) (x : Cohomology K Y n) :
    ordinarySingularCohomologyEquivGlobalRaw K Y n (c • x) =
      HomologicalComplex.homologyMap (globalRawSingularCochainComplexScalar K Y c) n
        (ordinarySingularCohomologyEquivGlobalRaw K Y n x) := by
  let S := (SingularChainComplex K Y).linearDualCochainComplex
  let T := (TopOpenSingularChainComplex K Y).linearDualCochainComplex
  let F := forget₂ (ModuleCat K) AddCommGrpCat
  let i := singularCochainComplexIsoTopOpen K Y
  have hsq : (globalRawSingularCochainComplexIso K Y).inv ≫ globalRawSingularCochainComplexScalar K Y c =
      (F.mapHomologicalComplex _).map (c • 𝟙 T) ≫ (globalRawSingularCochainComplexIso K Y).inv := by
    apply HomologicalComplex.Hom.ext
    funext m
    rfl
  have hi : (c • 𝟙 S) ≫ i.hom = i.hom ≫ (c • 𝟙 T) := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  have hmor : F.map (HomologicalComplex.homologyMap (c • 𝟙 S) n) ≫
      (F.map (HomologicalComplex.homologyMap i.hom n) ≫
        (topOpenForgottenSingularCochainHomologyIso K Y n).inv ≫
          HomologicalComplex.homologyMap (globalRawSingularCochainComplexIso K Y).inv n) =
      (F.map (HomologicalComplex.homologyMap i.hom n) ≫
        (topOpenForgottenSingularCochainHomologyIso K Y n).inv ≫
          HomologicalComplex.homologyMap (globalRawSingularCochainComplexIso K Y).inv n) ≫
        HomologicalComplex.homologyMap (globalRawSingularCochainComplexScalar K Y c) n := by
    rw [← Category.assoc, ← F.map_comp, ← HomologicalComplex.homologyMap_comp, hi,
      HomologicalComplex.homologyMap_comp, F.map_comp, Category.assoc,
      ← Category.assoc (F.map (HomologicalComplex.homologyMap (c • 𝟙 T) n)),
      topOpenForgottenSingularCochainHomologyIso_inv_naturality]
    simp only [Category.assoc]
    exact congrArg (fun g ↦ F.map (HomologicalComplex.homologyMap i.hom n) ≫
      (topOpenForgottenSingularCochainHomologyIso K Y n).inv ≫ g)
        (homologyMap_comp_of_comm hsq.symm n)
  have hx : c • x = (HomologicalComplex.homologyMap (c • 𝟙 S) n).hom x := by
    rw [homologyMap_smul_id]
    rfl
  rw [hx]
  exact ConcreteCategory.congr_hom hmor x

end Presheaf

section Int

variable (K : Type) [CommRing K] (X : Over (Spec ↧ℂ))

/-- Multiplication by `c : K` on the integer-indexed singular-cochain sheaf complex.

Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1. -/
def singularCochainSheafComplexIntScalar (c : K) :
    singularCochainSheafComplexInt X K ⟶ singularCochainSheafComplexInt X K :=
  HomologicalComplex.extendMap
    (singularCochainSheafComplexScalar K (TopCat.of (ComplexPoint X)) c) ComplexShape.embeddingUpNat

example (c : ℂ) :
    singularCochainSheafComplexIntScalar ℂ X c = HomologicalComplex.extendMap
      (singularCochainSheafComplexScalar ℂ (TopCat.of (ComplexPoint X)) c)
      ComplexShape.embeddingUpNat :=
  rfl

end Int

/-- The constants-to-cochains map intertwines `fieldScalarComplex` with multiplication by `c`. -/
lemma constantsToSingularCochainComplexInt_scalar (K : Type) [Field K] (X : Over (Spec ↧ℂ))
    (c : K) :
    constantsToSingularCochainComplexInt X K ≫ singularCochainSheafComplexIntScalar K X c =
      fieldScalarComplex K X c ≫ constantsToSingularCochainComplexInt X K := by
  have := congrArg (fun φ ↦ HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
    (constantsToSingularCochainSheafComplex_scalar K (TopCat.of (ComplexPoint X)) c)
  simp only [HomologicalComplex.extendMap_comp] at this
  exact this

/-- The inverse of the constants-to-cochains equivalence intertwines multiplication by `c` with
`fieldScalarComplex`. -/
lemma fieldHypercohomologySingularCochainAddEquiv_symm_scalar (K : Type) [Field K]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℤ) (c : K)
    (z : Hypercohomology X (singularCochainSheafComplexInt X K) n) :
    (fieldHypercohomologySingularCochainAddEquiv K X n).symm
        (hypercohomologyMap X (singularCochainSheafComplexIntScalar K X c) n z) =
      hypercohomologyMap X (fieldScalarComplex K X c) n
        ((fieldHypercohomologySingularCochainAddEquiv K X n).symm z) := by
  rw [AddEquiv.symm_apply_eq]
  obtain ⟨y, rfl⟩ := (fieldHypercohomologySingularCochainAddEquiv K X n).surjective z
  rw [AddEquiv.symm_apply_apply]
  change hypercohomologyMap X _ n (hypercohomologyMap X (constantsToSingularCochainComplexInt X K) n y) =
    hypercohomologyMap X (constantsToSingularCochainComplexInt X K) n
      (hypercohomologyMap X (fieldScalarComplex K X c) n y)
  have h1 := hypercohomologyMap_comp_apply X (constantsToSingularCochainComplexInt X K)
    (singularCochainSheafComplexIntScalar K X c) n y
  have h2 := hypercohomologyMap_comp_apply X (fieldScalarComplex K X c)
    (constantsToSingularCochainComplexInt X K) n y
  rw [constantsToSingularCochainComplexInt_scalar] at h1
  exact h1.symm.trans h2

/-- The comparison with Mathlib's sheaf cohomology carries `fieldScalarComplex` to the
`K`-module structure. -/
lemma hypercohomologyAddEquivConstantCohomology_scalar (K : Type) [Field K]
    (X : Over (Spec ↧ℂ)) (n : ℕ) (c : K)
    (y : Hypercohomology X (constantFieldSheafComplexInt K X) n) :
    hypercohomologyAddEquivConstantCohomology K X n
        (hypercohomologyMap X (fieldScalarComplex K X c) n y) =
      c • hypercohomologyAddEquivConstantCohomology K X n y := by
  apply (hypercohomologyAddEquivConstantCohomology K X n).symm.injective
  rw [AddEquiv.symm_apply_apply, hypercohomologyAddEquivConstantCohomology_symm_smul,
    AddEquiv.symm_apply_apply]


/-- A commutative square of complexes of abelian groups gives a commutative square in homology,
elementwise, for any complex shape. -/
lemma homologyMap_apply_of_comm' {ι : Type*} {s : ComplexShape ι}
    {A B C D : HomologicalComplex AddCommGrpCat s}
    {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D} (h : a ≫ b = c ≫ d) (n : ι)
    (x : A.homology n) :
    HomologicalComplex.homologyMap b n (HomologicalComplex.homologyMap a n x) =
      HomologicalComplex.homologyMap d n (HomologicalComplex.homologyMap c n x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, h]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Taking global sections commutes with extension by zero, compatibly with multiplication by
`c`. -/
lemma globalSectionsSingularCochainComplexIntIsoExtendField_scalar (K : Type) [CommRing K]
    (X : Over (Spec ↧ℂ)) (c : K) :
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map
          (singularCochainSheafComplexIntScalar K X c) ≫
        (globalSectionsSingularCochainComplexIntIsoExtendField K X).hom =
      (globalSectionsSingularCochainComplexIntIsoExtendField K X).hom ≫
        HomologicalComplex.extendMap
          (globalSingularCochainSheafComplexScalar K (TopCat.of (ComplexPoint X)) c)
          ComplexShape.embeddingUpNat := by
  dsimp only [globalSectionsSingularCochainComplexIntIsoExtendField,
    singularCochainSheafComplexIntScalar, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, HomologicalComplex.mapExtendCanonicalIso_naturality, Category.assoc,
    Category.assoc]
  congr 1
  change HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _ =
    HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  congr 1

/-- An endomorphism square through an isomorphism, inverted. -/
lemma inv_comp_eq_of_comp_hom {C : Type*} [Category* C] {A B : C} (i : A ≅ B) {a : A ⟶ A}
    {b : B ⟶ B} (h : a ≫ i.hom = i.hom ≫ b) : i.inv ≫ a = b ≫ i.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Scalar naturality of the named comparison: `singularToFieldCohomology K X n` commutes with
multiplication by every `c : K`. -/
theorem singularToFieldCohomology_smul (K : Type) [Field K] (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) (c : K)
    (x : AlgebraicTopology.Singular.Cohomology K (TopCat.of (ComplexPoint X)) n) :
    singularToFieldCohomology K X n (c • x) = c • singularToFieldCohomology K X n x := by
  let G := globalSingularCochainSheafComplex K (TopCat.of (ComplexPoint X))
  let Γ := (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor (TopCat.of (ComplexPoint X))).mapHomologicalComplex
    ℤᵘᵖ
  let iE := globalSectionsSingularCochainComplexIntIsoExtendField K X
  let jE := G.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl
  have hj : ∀ w, jE.inv (HomologicalComplex.homologyMap (globalSingularCochainSheafComplexScalar K (TopCat.of (ComplexPoint X)) c) n w) =
      HomologicalComplex.homologyMap (HomologicalComplex.extendMap
        (globalSingularCochainSheafComplexScalar K (TopCat.of (ComplexPoint X)) c) ComplexShape.embeddingUpNat) n (jE.inv w) := by
    intro w
    have h := HomologicalComplex.extendHomologyIso_hom_naturality
      (globalSingularCochainSheafComplexScalar K (TopCat.of (ComplexPoint X)) c) ComplexShape.embeddingUpNat (j := n) rfl
    rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq] at h
    exact (ConcreteCategory.congr_hom h w).symm
  have hiE := inv_comp_eq_of_comp_hom iE
    (globalSectionsSingularCochainComplexIntIsoExtendField_scalar K X c)
  change hypercohomologyAddEquivConstantCohomology K X n
      ((fieldHypercohomologySingularCochainAddEquiv K X n).symm
        (globalSectionsToHypercohomology X (singularCochainSheafComplexInt X K) n
          (HomologicalComplex.homologyMap iE.inv n (jE.inv
            (HomologicalComplex.homologyMap (topOpenToGlobalSingularCochainSheafComplex K (TopCat.of (ComplexPoint X))) n
              (ordinarySingularCohomologyEquivGlobalRaw K (TopCat.of (ComplexPoint X)) n (c • x))))))) =
    c • hypercohomologyAddEquivConstantCohomology K X n
      ((fieldHypercohomologySingularCochainAddEquiv K X n).symm
        (globalSectionsToHypercohomology X (singularCochainSheafComplexInt X K) n
          (HomologicalComplex.homologyMap iE.inv n (jE.inv
            (HomologicalComplex.homologyMap (topOpenToGlobalSingularCochainSheafComplex K (TopCat.of (ComplexPoint X))) n
              (ordinarySingularCohomologyEquivGlobalRaw K (TopCat.of (ComplexPoint X)) n x))))))
  rw [ordinarySingularCohomologyEquivGlobalRaw_smul,
    homologyMap_apply_of_comm' (topOpenToGlobalSingularCochainSheafComplex_scalar K (TopCat.of (ComplexPoint X)) c).symm, hj]
  erw [← homologyMap_apply_of_comm' hiE, globalSectionsToHypercohomology_naturality]
  rw [
    fieldHypercohomologySingularCochainAddEquiv_symm_scalar,
    hypercohomologyAddEquivConstantCohomology_scalar]

end HodgeLean.Foundations
