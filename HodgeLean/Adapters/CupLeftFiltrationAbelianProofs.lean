import HodgeLean.Adapters.CupLeftFiltrationAbelianDefs
import HodgeLean.Adapters.ResolutionClassAction
import HodgeLean.Adapters.CupLeftTransport
import HodgeLean.Adapters.HodgeFromCupLeft
import HodgeLean.Adapters.HolomorphicOneForms

/-! # Proof obligations for `CupLeftFiltrationAbelian`

One `_aux` per statement of `HodgeLean.Adapters.CupLeftFiltrationAbelian`, all open.
HC no distance; AV milestone no distance.
-/

noncomputable section

-- Boundary conversions between HQ and upstream sheaf cohomology have deep instance terms.
set_option maxRecDepth 4000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped TensorProduct

namespace HodgeLean.Adapters

local instance cupLeftFiltrationProofsHasDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- A morphism out of an integer-indexed cochain complex concentrated in degree `0`, built from its
degree-`0` component `g`; the only chain condition is `g ≫ d = 0` out of degree `0`.
Source: Mathlib's `HomologicalComplex.Hom` and `HomologicalComplex.XIsoOfEq`. -/
def homOfDegreeZero {V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    {A K : CochainComplex V ℤ} (hA : ∀ i ≠ 0, IsZero (A.X i)) (g : A.X 0 ⟶ K.X 0)
    (hg : g ≫ K.d 0 1 = 0) : A ⟶ K where
  f i := if h : i = 0 then (A.XIsoOfEq h).hom ≫ g ≫ (K.XIsoOfEq h).inv else 0
  comm' i j hij := by
    by_cases h : i = 0
    · subst h
      have hj : j = 1 := by simp at hij; omega
      subst hj
      simp only [↓reduceDIte, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv,
        Category.id_comp, Category.comp_id, hg]
      rw [(hA 1 one_ne_zero).eq_of_tgt (A.d 0 1) 0, zero_comp]
    · exact (hA i h).eq_of_src _ _

theorem homOfDegreeZero_f_zero {V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    {A K : CochainComplex V ℤ} (hA : ∀ i ≠ 0, IsZero (A.X i)) (g : A.X 0 ⟶ K.X 0)
    (hg : g ≫ K.d 0 1 = 0) : (homOfDegreeZero hA g hg).f 0 = g := by
  simp [homOfDegreeZero]

example {V : Type*} [Category V] [Limits.HasZeroMorphisms V] {A K : CochainComplex V ℤ}
    (hA : ∀ i ≠ 0, IsZero (A.X i)) : homOfDegreeZero hA (0 : A.X 0 ⟶ K.X 0) (zero_comp) = 0 := by
  ext i
  by_cases hi : i = 0
  · subst hi
    rw [homOfDegreeZero_f_zero]
    rfl
  · exact (hA i hi).eq_of_src _ _

/-- Morphisms out of a complex concentrated in degree `0` agree if they agree in degree `0`. -/
theorem hom_ext_of_degreeZero {V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    {A K : CochainComplex V ℤ} (hA : ∀ i ≠ 0, IsZero (A.X i)) {f g : A ⟶ K}
    (h : f.f 0 = g.f 0) : f = g := by
  ext i
  by_cases hi : i = 0
  · subst hi; exact h
  · exact (hA i hi).eq_of_src _ _

/-- `ℂ[0]` is zero outside degree `0`. -/
theorem constantComplexSheafComplexInt_isZero (X : Over (Spec ↧ℂ)) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((constantComplexSheafComplexInt X).X i) := by
  by_cases h : ∃ n : ℕ, ComplexShape.embeddingUpNat.f n = i
  · obtain ⟨n, rfl⟩ := h
    have hn : n ≠ 0 := by rintro rfl; exact hi rfl
    exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn).of_iso
      (HomologicalComplex.extendXIso _ _ rfl)
  · exact HomologicalComplex.isZero_extend_X _ _ _ (by simpa using h)

/-- `T'` is zero in degree `2`. -/
theorem primitiveComplex_isZero_two (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    IsZero ((primitiveComplex X).X ((2 : ℕ) : ℤ)) :=
  (HomologicalComplex.isZero_double_X _ _ 2 (by decide) (by decide)).of_iso
    (HomologicalComplex.extendXIso _ _ rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The degree-`0` component of `φ : ℂ[0] ⟶ Ω•[1]` lands in closed forms. -/
theorem deRhamShift_zero_comp_d (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (φ : constantComplexSheafComplexInt X ⟶ Ω•(X)⟦(1 : ℤ)⟧) :
    (φ.f 0 ≫ (wedgeThetaShiftXIso X 0).hom) ≫
      holomorphicDeRhamSheafDifferential X (dim X.left) 1 = 0 := by
  have h := φ.comm 0 1
  rw [(constantComplexSheafComplexInt_isZero X 1 one_ne_zero).eq_of_tgt
    ((constantComplexSheafComplexInt X).d 0 1) 0, zero_comp] at h
  change φ.f 0 ≫ ((1 : ℤ).negOnePow • (Ω•(X)).d (0 + 1) (1 + 1)) = 0 at h
  rw [Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.comp_neg, neg_eq_zero] at h
  have h2 : (Ω•(X)).d (0 + 1) (1 + 1) = _ :=
    HomologicalComplex.extend_d_eq (holomorphicDeRhamComplex X (dim X.left))
    ComplexShape.embeddingUpNat (i := 1) (j := 1 + 1) (i' := 0 + 1) (j' := 1 + 1) (by simp)
      (by simp)
  rw [holomorphicDeRhamComplex_d] at h2
  rw [h2] at h
  simp only [wedgeThetaShiftXIso, Iso.trans_hom, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.assoc]
  simp only [← Category.assoc, Preadditive.IsIso.comp_right_eq_zero] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem spec_exists_primitiveComplex_lift_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom]
    (φ : constantComplexSheafComplexInt X ⟶ Ω•(X)⟦(1 : ℤ)⟧) :
    ∃ j : constantComplexSheafComplexInt X ⟶ (primitiveComplex X)⟦(1 : ℤ)⟧,
      j ≫ (primitiveComplexToDeRham X)⟦(1 : ℤ)⟧' = φ := by
  have := spec_primitiveQuotientToClosedOneForm_isIso X
  let k : (constantComplexSheafComplexInt X).X 0 ⟶ primitiveQuotientSheaf X :=
    kernel.lift _ _ (deRhamShift_zero_comp_d X φ) ≫ inv (primitiveQuotientToClosedOneForm X)
  let g : (constantComplexSheafComplexInt X).X 0 ⟶ ((primitiveComplex X)⟦(1 : ℤ)⟧).X 0 :=
    k ≫ (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫
      ((primitiveComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).inv
  have hg : g ≫ ((primitiveComplex X)⟦(1 : ℤ)⟧).d 0 1 = 0 :=
    (primitiveComplex_isZero_two X).eq_of_tgt _ _
  refine ⟨homOfDegreeZero (constantComplexSheafComplexInt_isZero X) g hg, ?_⟩
  apply hom_ext_of_degreeZero (constantComplexSheafComplexInt_isZero X)
  rw [HomologicalComplex.comp_f, homOfDegreeZero_f_zero, CochainComplex.shiftFunctor_map_f']
  change g ≫ (primitiveComplexToClosedFormComplex X ≫ closedFormComplexToDeRham X).f
    ((1 : ℕ) : ℤ) = _
  rw [primitiveToDeRham_f_one]
  simp only [g, k, Category.assoc, Iso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc,
    kernel.lift_ι_assoc]
  simp [wedgeThetaShiftXIso]

section CupLeftFiltrationLift

open AlgebraicTopology.Simplicial AlgebraicTopology.Singular
open scoped Manifold

/-- Two morphisms out of a constant sheaf agree if they agree on the constant global sections. -/
theorem constSheaf_hom_ext {Y : TopCat.{0}} {A : AddCommGrpCat.{0}}
    {F : TopCat.Sheaf AddCommGrpCat Y} {f g : 𝓒[Y; A] ⟶ F}
    (h : ∀ a : A, f.hom.app (op ⊤) ((toSheafify (Opens.grothendieckTopology Y)
        𝓒ᵖ[Y; A]).app (op ⊤) a) =
      g.hom.app (op ⊤) ((toSheafify (Opens.grothendieckTopology Y) 𝓒ᵖ[Y; A]).app (op ⊤) a)) :
    f = g := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ F.property
  ext U a
  have hU := fun (k : 𝓒[Y; A] ⟶ F) ↦ NatTrans.naturality_apply
    (toSheafify (Opens.grothendieckTopology Y) 𝓒ᵖ[Y; A] ≫ k.hom) (homOfLE le_top : U.unop ⟶ ⊤).op a
  change (toSheafify (Opens.grothendieckTopology Y) 𝓒ᵖ[Y; A] ≫ f.hom).app U a =
    (toSheafify (Opens.grothendieckTopology Y) 𝓒ᵖ[Y; A] ≫ g.hom).app U a
  have e : (𝓒ᵖ[Y; A]).map (homOfLE le_top : U.unop ⟶ ⊤).op a = a := rfl
  rw [← e, hU f, hU g]
  exact congrArg _ (h a)

section Scalar

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- Multiplication by `c : ℂ` on the presheaf of holomorphic `p`-forms (each `HolomorphicForm X d U p`
is a `ℂ`-module and restriction is `ℂ`-linear).
Source: upstream `holomorphicFormRestriction` (a `ℂ`-linear map); Griffiths–Harris, *Principles of
Algebraic Geometry*, Ch. 0 §2. -/
def holomorphicFormPresheafScalar (c : ℂ) (p : ℕ) :
    holomorphicDeRhamPresheaf X d p ⟶ holomorphicDeRhamPresheaf X d p where
  app U := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (HolomorphicForm X d U p) c)
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    ext ω
    change HolomorphicForm X d U p at ω
    exact (map_smul (holomorphicFormRestriction X d i p) c ω).symm

example (p : ℕ) : holomorphicFormPresheafScalar X d 1 p = holomorphicFormPresheafScalar X d 1 p :=
  rfl

/-- Multiplication by `c : ℂ` on the constant presheaf `ℂ`.
Source: Mathlib's `Functor.const` and `AddMonoidHom.mulLeft`. -/
abbrev constPresheafScalar (Y : TopCat.{0}) (c : ℂ) : 𝓒ᵖ(Y; ℂ) ⟶ 𝓒ᵖ(Y; ℂ) :=
  (Functor.const _).map (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft c))

example (Y : TopCat.{0}) : constPresheafScalar Y 1 = constPresheafScalar Y 1 := rfl

theorem constantsToHolomorphicDeRhamZero_scalar (c : ℂ) :
    constantsToHolomorphicDeRhamZero X d ≫ holomorphicFormPresheafScalar X d c 0 =
      constPresheafScalar (TopCat.of (ComplexPoint X)) c ≫ constantsToHolomorphicDeRhamZero X d := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext a
  change ℂ at a
  change c • holomorphicFormOfConstant X d U a = holomorphicFormOfConstant X d U (c * a)
  exact (map_smul (holomorphicFormOfConstant X d U) c a).symm

theorem holomorphicDeRhamDifferential_scalar (c : ℂ) (p : ℕ) :
    holomorphicDeRhamDifferential X d p ≫ holomorphicFormPresheafScalar X d c (p + 1) =
      holomorphicFormPresheafScalar X d c p ≫ holomorphicDeRhamDifferential X d p := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext ω
  change HolomorphicForm X d U p at ω
  change c • holomorphicFormDifferential X d U p ω = holomorphicFormDifferential X d U p (c • ω)
  exact (map_smul (holomorphicFormDifferential X d U p) c ω).symm

theorem singularCochainCoboundary_scalar (Y : TopCat.{0}) (c : ℂ) (n : ℕ) :
    AlgebraicTopology.Singular.singularCochainCoboundary ℂ Y n ≫
        singularCochainPresheafScalar ℂ Y c (n + 1) =
      singularCochainPresheafScalar ℂ Y c n ≫
        AlgebraicTopology.Singular.singularCochainCoboundary ℂ Y n := by
  have h := (singularCochainPresheafComplexScalar ℂ Y c).comm n (n + 1)
  rw [AlgebraicTopology.Singular.singularCochainPresheafComplex_d] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- The value of `c θ` is `c` times the value of `θ`. -/
theorem globalFormValue_scalar (c : ℂ) (p : ℕ)
    (θ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤)) (x : ComplexPoint X) :
    globalFormValue X d p x (((presheafToSheaf (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) AddCommGrpCat).map
        (holomorphicFormPresheafScalar X d c p)).hom.app (op ⊤) θ) =
      c • globalFormValue X d p x θ := by
  obtain ⟨U, hx, ω, hω⟩ := spec_exists_local_representative X d p θ x
  have key : ∀ (ω : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d (op U)) p)
      (θ₀ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤)),
      (holomorphicDeRhamSheaf X d p).presheaf.map (homOfLE le_top : U ⟶ ⊤).op θ₀ =
        (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (holomorphicDeRhamPresheaf X d p)).app (op U) (Submodule.Quotient.mk ω) →
      globalFormValue X d p x θ₀ = holomorphicFormValueAt X d (op U) x hx p
        (Submodule.Quotient.mk ω) := by
    intro ω θ₀ h
    change _ = chartEvaluation X d (op U) x p ω (extChartAt 𝓘(ℂ, Fin d → ℂ) x x)
    rw [← spec_formStalkValue_germ_toSheafify X d p U x hx ω, ← h]
    change formStalkValue X d x p ((holomorphicDeRhamSheaf X d p).presheaf.germ ⊤ x trivial θ₀) = _
    rw [TopCat.Presheaf.germ_res_apply]
  rw [key ω θ hω, key (c • ω), Submodule.Quotient.mk_smul, map_smul]
  have hn := NatTrans.naturality_apply ((presheafToSheaf (Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))) AddCommGrpCat).map
      (holomorphicFormPresheafScalar X d c p)).hom (homOfLE le_top : U ⟶ ⊤).op θ
  erw [← hn, hω]
  have ht := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicFormPresheafScalar X d c p)) (op U))
    (Submodule.Quotient.mk ω : HolomorphicForm X d (op U) p)
  exact ht.symm

/-- Global holomorphic forms with the same values are equal. -/
theorem globalForm_ext (p : ℕ) (A B : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤))
    (h : ∀ x, globalFormValue X d p x A = globalFormValue X d p x B) : A = B := by
  rw [← sub_eq_zero]
  apply spec_eq_zero_of_globalFormValue_eq_zero X d p
  intro x
  rw [map_sub, h, sub_self]

end Scalar

section ScalarX

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

theorem functionValuePresheafMap_scalar (c : ℂ) :
    functionValuePresheafMap X ≫ singularCochainPresheafScalar ℂ _ c 0 =
      holomorphicFormPresheafScalar X (dim X.left) c 0 ≫ functionValuePresheafMap X := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext F
  change HolomorphicForm X (dim X.left) U 0 at F
  refine cochain_ext_chainOfSimplex _ _ fun σ ↦ ?_
  change c • functionValueCochain X U F (chainOfSimplex ℂ σ) =
    functionValueCochain X U (c • F) (chainOfSimplex ℂ σ)
  change c • simplexCochain ℂ _ 0 _ (chainOfSimplex ℂ σ) =
    simplexCochain ℂ _ 0 _ (chainOfSimplex ℂ σ)
  rw [spec_simplexCochain_chainOfSimplex, spec_simplexCochain_chainOfSimplex, map_smul]

local notation "Φ" X => presheafToSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
  AddCommGrpCat

/-- Multiplication by `c` on the sheaf `Ω^p`: the sheafification of `holomorphicFormPresheafScalar`.
Source: upstream `holomorphicDeRhamSheaf` (a sheafification); Mathlib's `presheafToSheaf`. -/
abbrev formSheafScalar (c : ℂ) (p : ℕ) :
    holomorphicDeRhamSheaf X (dim X.left) p ⟶ holomorphicDeRhamSheaf X (dim X.left) p :=
  (Φ X).map (holomorphicFormPresheafScalar X (dim X.left) c p)

example (p : ℕ) : formSheafScalar X 1 p = formSheafScalar X 1 p := rfl

/-- Multiplication by `c` on the constant sheaf `ℂ_X`: the sheafification of `constPresheafScalar`.
Source: Mathlib's `constantSheaf` and `presheafToSheaf`. -/
abbrev constSheafScalar (c : ℂ) : 𝓒(↧(ComplexPoint X); ℂ) ⟶ 𝓒(↧(ComplexPoint X); ℂ) :=
  (Φ X).map (constPresheafScalar (TopCat.of (ComplexPoint X)) c)

example : constSheafScalar X 1 = constSheafScalar X 1 := rfl

/-- Multiplication by `c` on the sheaf `S^n`: the sheafification of
`singularCochainPresheafScalar`.
Source: `HodgeLean.Foundations.singularCochainPresheafScalar`; Mathlib's `presheafToSheaf`. -/
abbrev singularSheafScalar (c : ℂ) (n : ℕ) :
    AlgebraicTopology.Singular.singularCochainSheaf ℂ (TopCat.of (ComplexPoint X)) n ⟶
      AlgebraicTopology.Singular.singularCochainSheaf ℂ (TopCat.of (ComplexPoint X)) n :=
  (Φ X).map (singularCochainPresheafScalar ℂ _ c n)

example (n : ℕ) : singularSheafScalar X 1 n = singularSheafScalar X 1 n := rfl

/-- Multiplication by `c` on `Ω^0/ℂ`, induced on the cokernel of `ℂ_X ⟶ Ω^0`.
Source: Mathlib's `CategoryTheory.Limits.cokernel.map`; `formSheafScalar`, `constSheafScalar`. -/
def primitiveQuotientScalar (c : ℂ) : primitiveQuotientSheaf X ⟶ primitiveQuotientSheaf X :=
  cokernel.map _ _ (constSheafScalar X c) (formSheafScalar X c 0) (by
    change (Φ X).map _ ≫ (Φ X).map _ = (Φ X).map _ ≫ (Φ X).map _
    rw [← Functor.map_comp, ← Functor.map_comp, constantsToHolomorphicDeRhamZero_scalar])

example : primitiveQuotientScalar X 1 = primitiveQuotientScalar X 1 := rfl

theorem pi_primitiveQuotientScalar (c : ℂ) :
    cokernel.π _ ≫ primitiveQuotientScalar X c = formSheafScalar X c 0 ≫ cokernel.π _ := by
  simp [primitiveQuotientScalar]

theorem primitiveQuotientScalar_comp_toOneForm (c : ℂ) :
    primitiveQuotientScalar X c ≫ primitiveQuotientToClosedOneForm X ≫ kernel.ι _ =
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _) ≫ formSheafScalar X c 1 := by
  have e1 : cokernel.π (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)) ≫
      primitiveQuotientToClosedOneForm X ≫ kernel.ι _ = (Φ X).map
        (holomorphicDeRhamDifferential X (dim X.left) 0) := by
    rw [primitiveQuotientToClosedOneForm, cokernel.π_desc_assoc, closedOneFormDifferential,
      kernel.lift_ι]
    rfl
  rw [← cancel_epi (cokernel.π _), reassoc_of% pi_primitiveQuotientScalar]
  simp only [Category.assoc]
  have key : (Φ X).map (holomorphicFormPresheafScalar X (dim X.left) c 0) ≫
      (Φ X).map (holomorphicDeRhamDifferential X (dim X.left) 0) =
      (Φ X).map (holomorphicDeRhamDifferential X (dim X.left) 0) ≫
        (Φ X).map (holomorphicFormPresheafScalar X (dim X.left) c 1) := by
    rw [← Functor.map_comp, ← Functor.map_comp, holomorphicDeRhamDifferential_scalar]
  rw [e1, reassoc_of% e1]
  exact key

theorem primitiveQuotientScalar_comp_toSingular (c : ℂ) :
    primitiveQuotientScalar X c ≫ primitiveQuotientToSingular X =
      primitiveQuotientToSingular X ≫ singularSheafScalar X c 1 := by
  have e1 : cokernel.π (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left)) ≫
      primitiveQuotientToSingular X = (Φ X).map
        (functionValuePresheafMap X ≫
          AlgebraicTopology.Singular.singularCochainCoboundary ℂ (TopCat.of (ComplexPoint X)) 0) := by
    rw [primitiveQuotientToSingular, cokernel.π_desc, Functor.map_comp]
    rfl
  have key : (Φ X).map (holomorphicFormPresheafScalar X (dim X.left) c 0) ≫ (Φ X).map
        (functionValuePresheafMap X ≫
          AlgebraicTopology.Singular.singularCochainCoboundary ℂ (TopCat.of (ComplexPoint X)) 0) =
      (Φ X).map (functionValuePresheafMap X ≫
          AlgebraicTopology.Singular.singularCochainCoboundary ℂ (TopCat.of (ComplexPoint X)) 0) ≫
        (Φ X).map (singularCochainPresheafScalar ℂ _ c 1) := by
    rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc,
      singularCochainCoboundary_scalar, reassoc_of% functionValuePresheafMap_scalar]
  rw [← cancel_epi (cokernel.π _), reassoc_of% pi_primitiveQuotientScalar, e1, reassoc_of% e1]
  exact key

end ScalarX

theorem globalSections_injective {Y : TopCat.{0}} {F G : TopCat.Sheaf AddCommGrpCat.{0} Y}
    (f : F ⟶ G) [Mono f] : Function.Injective (f.hom.app (op ⊤)) := by
  have := Functor.preservesMonomorphisms_of_adjunction
    (sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{0})
  have hf : Mono (C := Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) f := by
    exact ‹Mono f›
  have : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  have : Mono (f.hom.app (op ⊤)) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).1 this

section Degree0
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The degree-`0` component of `j : ℂ[0] ⟶ T'[1]`, as a map `ℂ_X ⟶ Ω^0/ℂ`.
Source: Mathlib's `HomologicalComplex.extendXIso` and `HomologicalComplex.doubleXIso₁`;
hl3's `constantCoefficientXZeroIso`. -/
abbrev liftComponent (j : constantComplexSheafComplexInt X ⟶ (primitiveComplex X)⟦(1 : ℤ)⟧) :
    𝓒(↧(ComplexPoint X); ℂ) ⟶ primitiveQuotientSheaf X :=
  (constantCoefficientXZeroIso X ℂ).inv ≫ j.f 0 ≫
    ((primitiveComplexNat X).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).hom ≫
      (HomologicalComplex.doubleXIso₁ _ _ (by decide)).hom

example (j : constantComplexSheafComplexInt X ⟶ (primitiveComplex X)⟦(1 : ℤ)⟧) :
    liftComponent X j = liftComponent X j := rfl

set_option backward.isDefEq.respectTransparency false in
theorem liftComponent_comp_toSingular
    (j : constantComplexSheafComplexInt X ⟶ (primitiveComplex X)⟦(1 : ℤ)⟧) :
    (constantCoefficientXZeroIso X ℂ).inv ≫ (j ≫ (primitiveComplexToSingular X)⟦(1 : ℤ)⟧').f 0 =
      liftComponent X j ≫ primitiveQuotientToSingular X ≫
        ((AlgebraicTopology.Singular.singularCochainSheafComplex ℂ
          (TopCat.of (ComplexPoint X))).extendXIso ComplexShape.embeddingUpNat
          (i := 1) rfl).inv := by
  rw [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']
  change _ ≫ _ ≫ (primitiveComplexToSingular X).f ((1 : ℕ) : ℤ) = _
  rw [primitiveToSingular_f_one]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem liftComponent_comp_toOneForm (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧)
    (j : constantComplexSheafComplexInt X ⟶ (primitiveComplex X)⟦(1 : ℤ)⟧)
    (hj : j ≫ (primitiveComplexToDeRham X)⟦(1 : ℤ)⟧' =
      constantsToHolomorphicDeRhamComplexInt X ≫ L) :
    liftComponent X j ≫ primitiveQuotientToClosedOneForm X ≫ kernel.ι _ =
      (constantCoefficientXZeroIso X ℂ).inv ≫
        (constantsToHolomorphicDeRhamComplexInt X ≫ L).f ((0 : ℕ) : ℤ) ≫
          (wedgeThetaShiftXIso X 0).hom := by
  have h := congrArg (fun f ↦ (constantCoefficientXZeroIso X ℂ).inv ≫ f.f 0 ≫
    (wedgeThetaShiftXIso X 0).hom) hj
  refine Eq.trans ?_ h
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']
  change _ = _ ≫ (_ ≫ (primitiveComplexToClosedFormComplex X ≫ closedFormComplexToDeRham X).f
    ((1 : ℕ) : ℤ)) ≫ _
  rw [primitiveToDeRham_f_one]
  simp [wedgeThetaShiftXIso]

end Degree0

theorem isoTopOpen_eq_cupLeftRestrict {Y : TopCat.{0}} {n : ℕ}
    (a : Cochain ℂ (TopCat.toSSet.obj Y) n) :
    ((singularCochainComplexIsoTopOpen ℂ Y).hom.f n).hom a = cupLeftRestrict a (op ⊤) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem constantsToSingular_comp_cupLeft_f_zero (X : Over (Spec ↧ℂ))
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1) :
    (constantCoefficientXZeroIso X ℂ).inv ≫
        (constantsToSingularCochainComplexInt X ℂ ≫ cupLeftComplexHom X Ψ).f 0 =
      (constantsToSingularCochainZeroSheaf ℂ (TopCat.of (ComplexPoint X)) ≫
        cupLeftSheafHom Ψ.1 0) ≫
        ((AlgebraicTopology.Singular.singularCochainSheafComplex ℂ
          (TopCat.of (ComplexPoint X))).extendXIso ComplexShape.embeddingUpNat
          (i := 1) rfl).inv := by
  rw [HomologicalComplex.comp_f]
  change _ ≫ (constantsToSingularCochainComplexInt X ℂ).f ((0 : ℕ) : ℤ) ≫
    cupLeftSheafComplexHomF Ψ.1 ((0 : ℕ) : ℤ) = _
  have h := HomologicalComplex.extendMap_f
    (constantsToSingularCochainSheafComplex ℂ (TopCat.of (ComplexPoint X)))
    ComplexShape.embeddingUpNat (i := 0) (i' := ((0 : ℕ) : ℤ)) rfl
  rw [cupLeftSheafComplexHomF_natCast]
  erw [h]
  simp [constantCoefficientXZeroIso, constantsToSingularCochainSheafComplex, cupLeftSheafHomX]

set_option backward.isDefEq.respectTransparency false in
theorem liftComponent_comp_toSingular_eq (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (θ : GlobalHolomorphicForm X 1)
    (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (hθ' : ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = θ)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : globalCochainSection X 1 Ψ.1 =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (primitiveQuotientToSingular X)).hom θ')
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X θ L)
    (j : constantComplexSheafComplexInt X ⟶ (primitiveComplex X)⟦(1 : ℤ)⟧)
    (hj : j ≫ (primitiveComplexToDeRham X)⟦(1 : ℤ)⟧' =
      constantsToHolomorphicDeRhamComplexInt X ≫ L) :
    liftComponent X j ≫ primitiveQuotientToSingular X =
      constantsToSingularCochainZeroSheaf ℂ (TopCat.of (ComplexPoint X)) ≫
        cupLeftSheafHom Ψ.1 0 := by
  have := spec_primitiveQuotientToClosedOneForm_isIso X
  apply constSheaf_hom_ext
  intro a
  change ℂ at a
  have hs : (liftComponent X j).hom.app (op ⊤)
      ((toSheafify (Opens.grothendieckTopology _) 𝓒ᵖ(↧(ComplexPoint X); ℂ)).app (op ⊤) a) =
      (primitiveQuotientScalar X a).hom.app (op ⊤) θ' := by
    apply globalSections_injective (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)
    refine globalForm_ext X (dim X.left) 1 _ _ fun x ↦ ?_
    have hW : (primitiveQuotientToClosedOneForm X ≫ kernel.ι _).hom.app (op ⊤)
        ((liftComponent X j).hom.app (op ⊤)
          ((toSheafify (Opens.grothendieckTopology _) 𝓒ᵖ(↧(ComplexPoint X); ℂ)).app (op ⊤) a)) =
        ((constantCoefficientXZeroIso X ℂ).inv ≫
          (constantsToHolomorphicDeRhamComplexInt X ≫ L).f ((0 : ℕ) : ℤ) ≫
            (wedgeThetaShiftXIso X 0).hom).hom.app (op ⊤) (constantGlobalSection X ℂ a) := by
      rw [← liftComponent_comp_toOneForm X L j hj]
      rfl
    have hM : (primitiveQuotientToClosedOneForm X ≫ kernel.ι _).hom.app (op ⊤)
        ((primitiveQuotientScalar X a).hom.app (op ⊤) θ') =
        (formSheafScalar X a 1).hom.app (op ⊤) θ := by
      rw [← hθ']
      change ((primitiveQuotientScalar X a ≫ primitiveQuotientToClosedOneForm X ≫
        kernel.ι _).hom.app (op ⊤)) θ' = _
      rw [primitiveQuotientScalar_comp_toOneForm]
      rfl
    rw [hW, hM]
    refine Eq.trans ?_ (globalFormValue_scalar X _ a 1 θ x).symm
    apply (ContinuousAlternatingMap.ofSubsingleton ℂ (Fin (dim X.left) → ℂ) ℂ (0 : Fin 1)).symm.injective
    refine (spec_constantsToHolomorphicDeRham_comp_wedgeTheta_value X θ L hL a x).trans ?_
    ext u
    rfl
  have hLeft : (liftComponent X j ≫ primitiveQuotientToSingular X).hom.app (op ⊤)
      ((toSheafify (Opens.grothendieckTopology _) 𝓒ᵖ(↧(ComplexPoint X); ℂ)).app (op ⊤) a) =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (singularCochainPresheaf ℂ (TopCat.of (ComplexPoint X)) 1)).app (op ⊤)
          (a • cupLeftRestrict Ψ.1 (op ⊤)) := by
    change (primitiveQuotientToSingular X).hom.app (op ⊤) ((liftComponent X j).hom.app (op ⊤)
      ((toSheafify (Opens.grothendieckTopology _) 𝓒ᵖ(↧(ComplexPoint X); ℂ)).app (op ⊤) a)) = _
    rw [hs]
    change ((primitiveQuotientScalar X a ≫ primitiveQuotientToSingular X).hom.app (op ⊤)) θ' = _
    rw [primitiveQuotientScalar_comp_toSingular]
    change (singularSheafScalar X a 1).hom.app (op ⊤)
      ((primitiveQuotientToSingular X).hom.app (op ⊤) θ') = _
    erw [← hΨ]
    rw [spec_globalCochainSection_eq_toSheafify, isoTopOpen_eq_cupLeftRestrict]
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (singularCochainPresheafScalar ℂ _ a 1)) (op ⊤)) _).symm
  have hRight : (constantsToSingularCochainZeroSheaf ℂ (TopCat.of (ComplexPoint X)) ≫
        cupLeftSheafHom Ψ.1 0).hom.app (op ⊤)
      ((toSheafify (Opens.grothendieckTopology _) 𝓒ᵖ(↧(ComplexPoint X); ℂ)).app (op ⊤) a) =
      (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (singularCochainPresheaf ℂ (TopCat.of (ComplexPoint X)) 1)).app (op ⊤)
          (a • cupLeftRestrict Ψ.1 (op ⊤)) := by
    have e : constantsToSingularCochainZeroSheaf ℂ (TopCat.of (ComplexPoint X)) ≫
        cupLeftSheafHom Ψ.1 0 = (presheafToSheaf (Opens.grothendieckTopology
          (TopCat.of (ComplexPoint X))) AddCommGrpCat).map
        (constantsToSingularCochainZero ℂ (TopCat.of (ComplexPoint X)) ≫
          cupLeftPresheafHom Ψ.1 0) := by
      rw [Functor.map_comp]
      rfl
    rw [e]
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (constantsToSingularCochainZero ℂ (TopCat.of (ComplexPoint X)) ≫
          cupLeftPresheafHom Ψ.1 0)) (op ⊤)) a
    refine h.symm.trans ?_
    rw [← spec_cupLeftPresheafHom_constants Ψ.1 (op ⊤) a]
    rfl
  exact hLeft.trans hRight.symm

end CupLeftFiltrationLift

set_option backward.isDefEq.respectTransparency false in
theorem spec_primitiveComplex_lift_comp_toSingular_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (θ : GlobalHolomorphicForm X 1)
    (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (hθ' : ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = θ)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : globalCochainSection X 1 Ψ.1 =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (primitiveQuotientToSingular X)).hom θ')
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X θ L)
    (j : constantComplexSheafComplexInt X ⟶ (primitiveComplex X)⟦(1 : ℤ)⟧)
    (hj : j ≫ (primitiveComplexToDeRham X)⟦(1 : ℤ)⟧' =
      constantsToHolomorphicDeRhamComplexInt X ≫ L) :
    j ≫ (primitiveComplexToSingular X)⟦(1 : ℤ)⟧' =
      constantsToSingularCochainComplexInt X ℂ ≫ cupLeftComplexHom X Ψ := by
  apply hom_ext_of_degreeZero (constantComplexSheafComplexInt_isZero X)
  rw [← cancel_epi (constantCoefficientXZeroIso X ℂ).inv, liftComponent_comp_toSingular,
    constantsToSingular_comp_cupLeft_f_zero, ← Category.assoc,
    liftComponent_comp_toSingular_eq X θ θ' hθ' Ψ hΨ L hL j hj]

theorem spec_resolutionClass_comp_mk₀_eq_mk_of_lift_aux (X : Over (Spec ↧ℂ))
    {A K T : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (q : A ⟶ K)
    (hq : analyticQuasiIsomorphisms X q) (q' : A ⟶ T) (p : T ⟶ K)
    (hp : analyticQuasiIsomorphisms X p) (hqp : q' ≫ p = q) (L : K ⟶ K⟦(1 : ℤ)⟧)
    (j : A ⟶ T⟦(1 : ℤ)⟧) (hj : j ≫ p⟦(1 : ℤ)⟧' = q ≫ L) :
    (resolutionClass X q hq L).comp
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl q')
        (zero_add 1) =
      Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom A T (1 : ℤ) from j) := by
  apply (Localization.SmallShiftedHom.postcompEquiv p hp (X := A) (a := (1 : ℤ))).injective
  apply (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q).injective
  have h1 := congrArg (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q) (spec_resolutionClass_comp_mk₀ X q hq L)
  simp only [Localization.SmallShiftedHom.postcompEquiv_apply,
    Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk,
    Localization.SmallShiftedHom.equiv_mk₀] at h1 ⊢
  rw [ShiftedHom.comp_assoc _ _ _ (zero_add _) (add_zero _) (by simp), ShiftedHom.mk₀_comp_mk₀,
    ← Functor.map_comp, hqp, h1, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  simp only [ShiftedHom.map]
  rw [Category.assoc, ← Functor.commShiftIso_hom_naturality, ← Functor.map_comp_assoc, ← hj]
  simp only [Functor.map_comp, Category.assoc]

theorem spec_resolutionClass_wedgeTheta_eq_cupLeft_of_primitive_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (θ : GlobalHolomorphicForm X 1)
    (θ' : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).obj (primitiveQuotientSheaf X))
    (hθ' : ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
      (primitiveQuotientToClosedOneForm X ≫ kernel.ι _)).hom θ' = θ)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : globalCochainSection X 1 Ψ.1 =
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map (primitiveQuotientToSingular X)).hom θ')
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X θ L) :
    resolutionClass X (constantsToHolomorphicDeRhamComplexInt X)
        (constantsToHolomorphicDeRham_mem X) L =
      resolutionClass X (constantsToSingularCochainComplexInt X ℂ)
        (constantsToSingularCochain_mem X ℂ) (cupLeftComplexHom X Ψ) := by
  obtain ⟨j, hj⟩ := spec_exists_primitiveComplex_lift_aux X
    (constantsToHolomorphicDeRhamComplexInt X ≫ L)
  have hj' := spec_primitiveComplex_lift_comp_toSingular_aux X θ θ' hθ' Ψ hΨ L hL j hj
  have e1 := spec_resolutionClass_comp_mk₀_eq_mk_of_lift_aux X _
    (constantsToHolomorphicDeRham_mem X) (constantsToPrimitiveComplex X)
    (primitiveComplexToDeRham X) (primitiveComplexToDeRham_mem X)
    (constantsToPrimitiveComplex_comp_toDeRham X) L j hj
  have e2 := spec_resolutionClass_comp_mk₀_eq_mk_of_lift_aux X _
    (constantsToSingularCochain_mem X ℂ) (constantsToPrimitiveComplex X)
    (primitiveComplexToSingular X) (primitiveComplexToSingular_mem X)
    (spec_constantsToPrimitiveComplex_comp_toSingular X) (cupLeftComplexHom X Ψ) j hj'
  apply (Localization.SmallShiftedHom.postcompEquiv (constantsToPrimitiveComplex X)
    (constantsToPrimitiveComplex_mem X) (a := (1 : ℤ))).injective
  exact e1.trans e2.symm

theorem spec_resolutionClass_wedgeTheta_eq_cupLeft_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z))
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X (cycleOneForm X z) L) :
    resolutionClass X (constantsToHolomorphicDeRhamComplexInt X)
        (constantsToHolomorphicDeRham_mem X) L =
      resolutionClass X (constantsToSingularCochainComplexInt X ℂ)
        (constantsToSingularCochain_mem X ℂ) (cupLeftComplexHom X Ψ) := by
  have hθ : cycleOneForm X z ∈ closedGlobalHolomorphicOneForms X := by
    rw [← spec_range_cycleOneForm X]
    exact ⟨z, rfl⟩
  obtain ⟨θ', hθ'⟩ := spec_exists_globalPrimitive_of_closed X _ hθ
  exact spec_resolutionClass_wedgeTheta_eq_cupLeft_of_primitive_aux X _ θ' hθ' Ψ
    (by rw [hΨ]; exact spec_globalCochainSection_singularIntegrationCochain X _ θ' hθ') L hL

theorem spec_fieldToDeRham_sheafHypercohomologyFieldEquiv_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (β : Hypercohomology X (singularCochainSheafComplexInt X ℂ) n) :
    fieldToDeRhamCohomology ℂ X n (sheafHypercohomologyFieldEquiv ℂ X n β) =
      hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) n
        ((Localization.SmallShiftedHom.postcompEquiv (constantsToSingularCochainComplexInt X ℂ)
          (constantsToSingularCochain_mem X ℂ)).symm β) := by
  rw [fieldToDeRhamCohomology_complex_eq]
  unfold sheafHypercohomologyFieldEquiv
  rw [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  rfl

theorem spec_hypercohomologyMap_comp_wedgeTheta_eq_cupLeft_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom]
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧)
    (he : resolutionClass X (constantsToHolomorphicDeRhamComplexInt X)
        (constantsToHolomorphicDeRham_mem X) L =
      resolutionClass X (constantsToSingularCochainComplexInt X ℂ)
        (constantsToSingularCochain_mem X ℂ) (cupLeftComplexHom X Ψ))
    {k m : ℤ} (h : 1 + k = m) (β : Hypercohomology X (singularCochainSheafComplexInt X ℂ) k) :
    hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) m
        ((Localization.SmallShiftedHom.postcompEquiv (constantsToSingularCochainComplexInt X ℂ)
          (constantsToSingularCochain_mem X ℂ)).symm (cupLeftHypercohomology X Ψ h β)) =
      (hypercohomologyMap X (constantsToHolomorphicDeRhamComplexInt X) k
        ((Localization.SmallShiftedHom.postcompEquiv (constantsToSingularCochainComplexInt X ℂ)
          (constantsToSingularCochain_mem X ℂ)).symm β)).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (show ShiftedHom Ω•(X) Ω•(X) (1 : ℤ) from L)) h := by
  set α := (Localization.SmallShiftedHom.postcompEquiv (constantsToSingularCochainComplexInt X ℂ)
    (constantsToSingularCochain_mem X ℂ)).symm β with hα
  have hβ : β = hypercohomologyMap X (constantsToSingularCochainComplexInt X ℂ) k α :=
    ((Localization.SmallShiftedHom.postcompEquiv (constantsToSingularCochainComplexInt X ℂ)
      (constantsToSingularCochain_mem X ℂ)).apply_symm_apply β).symm
  have h1 : cupLeftHypercohomology X Ψ h β =
      hypercohomologyMap X (constantsToSingularCochainComplexInt X ℂ) m
        (α.comp (resolutionClass X (constantsToSingularCochainComplexInt X ℂ)
          (constantsToSingularCochain_mem X ℂ) (cupLeftComplexHom X Ψ)) h) := by
    rw [spec_hypercohomologyMap_comp_resolutionClass, ← hβ]
    rfl
  rw [h1]
  have h2 := (Localization.SmallShiftedHom.postcompEquiv
    (constantsToSingularCochainComplexInt X ℂ) (constantsToSingularCochain_mem X ℂ)).symm_apply_apply
    (α.comp (resolutionClass X (constantsToSingularCochainComplexInt X ℂ)
      (constantsToSingularCochain_mem X ℂ) (cupLeftComplexHom X Ψ)) h)
  erw [h2]
  have h3 := spec_hypercohomologyMap_comp_resolutionClass X
    (constantsToHolomorphicDeRhamComplexInt X) (constantsToHolomorphicDeRham_mem X) L h α
  rw [he] at h3
  exact h3

theorem spec_deRham_cupLeftHypercohomology_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z))
    (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (hL : IsWedgeThetaHom X (cycleOneForm X z) L)
    (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ))
    (β : Hypercohomology X (singularCochainSheafComplexInt X ℂ) k) :
    fieldToDeRhamCohomology ℂ X (1 + k)
        (sheafHypercohomologyFieldEquiv ℂ X (1 + k) (cupLeftHypercohomology X Ψ h β)) =
      (fieldToDeRhamCohomology ℂ X k (sheafHypercohomologyFieldEquiv ℂ X k β)).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (show ShiftedHom Ω•(X) Ω•(X) (1 : ℤ) from L)) h := by
  rw [spec_fieldToDeRham_sheafHypercohomologyFieldEquiv_aux,
    spec_fieldToDeRham_sheafHypercohomologyFieldEquiv_aux]
  exact spec_hypercohomologyMap_comp_wedgeTheta_eq_cupLeft_aux X Ψ L
    (spec_resolutionClass_wedgeTheta_eq_cupLeft_aux X z Ψ hΨ L hL) h β

theorem spec_comp_mem_hodgeFiltration_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (L : Ω•(X) ⟶ Ω•(X)⟦(1 : ℤ)⟧) (q : ℤ) {k m : ℤ} (h : 1 + k = m)
    (α : H_dR^k(X)) (hα : α ∈ F^q H_dR^k(X)) :
    α.comp (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom Ω•(X) Ω•(X) (1 : ℤ) from L)) h ∈ F^(1 + q) H_dR^m(X) := by
  obtain rfl : m = k + 1 := by omega
  have hmem := spec_hypercohomologyShift_mem_hodgeFiltration X L q k α hα
  rw [spec_hypercohomologyShift_hypercohomologyMap_eq_comp, add_comm q 1] at hmem
  exact hmem

theorem spec_complexSingularClass_eq_smul_integrationClass_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (q : ℚ)
    (hq : ∀ v : HQ X 1,
      singularToFieldCohomology ℚ X 1 (cupComparison X 1 v) = q • HQ.linearEquiv X 1 v)
    (x : ℂ ⊗[ℚ] HQ X 1) (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (hx : bettiDeRhamHQ X 1 x = cycleDeRhamClass X z)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (hΨ : Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z)) :
    complexSingularClass X 1 x =
      (q : ℂ) • Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ := by
  have (U : Opens (ComplexPoint X)) : ParacompactSpace U := openParacompactSpace X U
  have key : ∀ ω : ℂ ⊗[ℚ] HQ X 1, fieldToDeRhamCohomology ℂ X 1
      (singularToFieldCohomology ℂ X 1 (complexSingularClass X 1 ω)) =
        (q : ℂ) • bettiDeRhamHQ X 1 ω := by
    intro ω
    induction ω using TensorProduct.inductionOn with
    | tmul a v =>
      change fieldToDeRhamCohomology ℂ X 1 (singularToFieldCohomology ℂ X 1
        (cohomologyBaseChange (TopCat.of (ComplexPoint X)) 1 (a ⊗ₜ cupComparison X 1 v))) = _
      rw [bettiDeRhamHQ_tmul,
        fieldToDeRham_singularToFieldCohomology_cohomologyBaseChange_tmul X 1 q hq a v]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  apply (spec_singularToFieldCohomology_bijective ℂ X 1).injective
  apply (spec_fieldToDeRhamCohomology_complex_bijective X 1).injective
  rw [key, hx, spec_singularToFieldCohomology_smul, fieldToDeRhamCohomology_smul,
    spec_deRham_singularIntegrationCochain X z Ψ hΨ]

theorem spec_cupLeft_cupProductOf_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m ((cupProductOf X).cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X) := by
  intro k m h q x y hx hy
  subst h
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  have hr : bettiDeRhamHQ X 1 x ∈ (cycleDeRhamClass X).range := by
    rw [← spec_hodgeFiltration_one_eq_range_cycleDeRhamClass X]
    exact hx
  obtain ⟨z, hz⟩ := hr
  let Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
      (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1 :=
    ⟨_, spec_coboundary_singularIntegrationCochain X (dim X.left) (cycleOneForm X z)⟩
  obtain ⟨r, hr0, hrq⟩ := spec_singularToFieldCohomology_cupComparison X 1
  have hκ := spec_complexSingularClass_eq_smul_integrationClass_aux X r hrq x z hz.symm Ψ rfl
  have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
  set x' : ℂ ⊗[ℚ] HQ X 1 := (r : ℂ)⁻¹ • x with hx'
  have hκ' : Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ =
      complexSingularClass X 1 x' := by
    rw [hx', LinearMap.map_smul, hκ, smul_smul, inv_mul_cancel₀ hr0', one_smul]
  have hxx : x = (r : ℂ) • x' := by
    rw [hx', smul_smul, mul_inv_cancel₀ hr0', one_smul]
  have hθ : cycleOneForm X z ∈ closedGlobalHolomorphicForms X 1 := by
    rw [show closedGlobalHolomorphicForms X 1 = closedGlobalHolomorphicOneForms X from rfl,
      ← spec_range_cycleOneForm X]
    exact ⟨z, rfl⟩
  obtain ⟨L, hL⟩ := spec_exists_isWedgeThetaHom X _ hθ
  obtain ⟨c, -, hc⟩ := spec_bettiDeRhamHQ_cupC_eq_smul_deRham_cupLeft X
  have h' : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨s, -, hs⟩ := spec_deRham_singularToFieldCohomology_cohomologyBaseChange X k
  have hβ : fieldToDeRhamCohomology ℂ X k (sheafHypercohomologyFieldEquiv ℂ X k
      (singularToSheafHypercohomology X ℂ k (complexSingularClass X k y))) ∈
      F^q H_dR^(k : ℤ)(X) := by
    change fieldToDeRhamCohomology ℂ X k (singularToFieldCohomology ℂ X k
      (cohomologyBaseChange (TopCat.of (ComplexPoint X)) k
        (LinearMap.baseChange ℂ (cupComparison X k).toLinearMap y))) ∈ _
    rw [hs y]
    exact Submodule.smul_mem _ _ hy
  have hmem := spec_comp_mem_hodgeFiltration_aux X L q h' _ hβ
  rw [← spec_deRham_cupLeftHypercohomology_aux X z Ψ rfl L hL k h'] at hmem
  rw [hxx, LinearMap.map_smul₂, LinearMap.map_smul, hc k h' x' Ψ hκ' y]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hmem)

end HodgeLean.Adapters
