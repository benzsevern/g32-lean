import HodgeLean.Foundations.Algebraic.GrassmannianDefs

/-! # Grassmannian sheaf lane: matrices between free sheaves of modules on a scheme

On a scheme `X`, a global function `a ∈ Γ(X, ⊤)` acts on the unit sheaf `𝒪_X` by multiplication
(`f5sheaf_scal`), and every endomorphism of `𝒪_X` is of this form. A matrix `Y` with entries in
`Γ(X, ⊤)` and columns indexed by `ι` gives the morphism of free sheaves `𝒪^ι ⟶ 𝒪^κ` sending the
`j`-th generator to `∑ᵢ Y i j • eᵢ` (`f5sheaf_matHom`). For finite `κ`, every morphism between
free sheaves is the morphism of exactly one matrix, and composition is matrix multiplication.
The pullback along `f : X' ⟶ X` of the morphism of `Y` is, through the identification of pullbacks
of free sheaves with free sheaves, the morphism of the matrix `f^♯ Y` with entries pulled back by
`f.appTop`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace HodgeLean.Foundations.Algebraic

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}}

/-- The unit sheaf `𝒪_X`, as an object of `X.Modules`.
Source: EGA 0_I, §4.1.1. -/
abbrev f5sheaf_unit (X : Scheme.{0}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The free sheaf `𝒪_X^I`, as an object of `X.Modules`.
Source: EGA 0_I, §5.4.1. -/
abbrev f5sheaf_free (X : Scheme.{0}) (I : Type) : X.Modules := SheafOfModules.free I

/-- The inclusion of the factor of index `i` into the free sheaf.
Source: EGA 0_I, §5.4.1. -/
def f5sheaf_ιFree {I : Type} (i : I) : f5sheaf_unit X ⟶ f5sheaf_free X I :=
  SheafOfModules.ιFree i

theorem f5sheaf_free_hom_ext {ι : Type} {M : X.Modules} {f g : f5sheaf_free X ι ⟶ M}
    (h : ∀ j, f5sheaf_ιFree j ≫ f = f5sheaf_ιFree j ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan ι) f g h

/-! ### Scalars acting on the unit sheaf -/

/-- The section of the unit sheaf given by a global function, restricted to every open.
Source: EGA 0_I, §4.1.3 (sections of `𝒪_X`). -/
def f5sheaf_unitSection (a : Γ(X, ⊤)) : (SheafOfModules.unit X.ringCatSheaf).sections :=
  PresheafOfModules.sectionsMk (fun U => (X.presheaf.map (homOfLE le_top).op a : Γ(X, U.unop)))
    (fun U V f => by
      change X.presheaf.map f (X.presheaf.map _ a) = _
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl)

theorem f5sheaf_unitSection_val (a : Γ(X, ⊤)) (U : X.Opensᵒᵖ) :
    (f5sheaf_unitSection a).val U = X.presheaf.map (homOfLE le_top).op a := rfl

/-- The value of a section of the unit sheaf on the whole scheme.
Source: EGA 0_I, §3.2.1 (sections of a sheaf over the whole space). -/
def f5sheaf_sectionTop (s : (SheafOfModules.unit X.ringCatSheaf).sections) : Γ(X, ⊤) :=
  s.val (Opposite.op ⊤)

theorem f5sheaf_unitSection_sectionTop (s : (SheafOfModules.unit X.ringCatSheaf).sections) :
    f5sheaf_unitSection (f5sheaf_sectionTop s) = s := by
  apply PresheafOfModules.sections_ext
  intro U
  exact s.property (homOfLE (le_top : U.unop ≤ ⊤)).op

theorem f5sheaf_sectionTop_unitSection (a : Γ(X, ⊤)) :
    f5sheaf_sectionTop (f5sheaf_unitSection a) = a :=
  CategoryTheory.congr_fun (X.presheaf.map_id _) a

/-- Multiplication by a global function, as an endomorphism of the unit sheaf.
Source: EGA 0_I, §4.1.1 (`𝒪_X`-modules); Stacks Project, Tag 01AD. -/
def f5sheaf_scal (a : Γ(X, ⊤)) : f5sheaf_unit X ⟶ f5sheaf_unit X :=
  (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm (f5sheaf_unitSection a)

theorem f5sheaf_scal_app (a : Γ(X, ⊤)) (U : X.Opensᵒᵖ) (r : Γ(X, U.unop)) :
    (f5sheaf_scal a).val.app U r = r * X.presheaf.map (homOfLE le_top).op a := rfl

/-- The scalar of an endomorphism of the unit sheaf: the image of `1` over the whole scheme.
Source: EGA 0_I, §4.1.1. -/
def f5sheaf_scalOf (f : f5sheaf_unit X ⟶ f5sheaf_unit X) : Γ(X, ⊤) :=
  f5sheaf_sectionTop ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv f)

theorem f5sheaf_scal_scalOf (f : f5sheaf_unit X ⟶ f5sheaf_unit X) :
    f5sheaf_scal (f5sheaf_scalOf f) = f := by
  rw [f5sheaf_scal, f5sheaf_scalOf, f5sheaf_unitSection_sectionTop, Equiv.symm_apply_apply]

theorem f5sheaf_scalOf_scal (a : Γ(X, ⊤)) : f5sheaf_scalOf (f5sheaf_scal a) = a := by
  rw [f5sheaf_scal, f5sheaf_scalOf, Equiv.apply_symm_apply, f5sheaf_sectionTop_unitSection]

theorem f5sheaf_scal_injective : Function.Injective (f5sheaf_scal (X := X)) :=
  fun a b h => by rw [← f5sheaf_scalOf_scal a, h, f5sheaf_scalOf_scal]

theorem f5sheaf_scalOf_eq (f : f5sheaf_unit X ⟶ f5sheaf_unit X) :
    f5sheaf_scalOf f = f.val.app (Opposite.op ⊤) (1 : Γ(X, ⊤)) := rfl

theorem f5sheaf_scal_top (a r : Γ(X, ⊤)) :
    (f5sheaf_scal a).val.app (Opposite.op ⊤) r = r * a := by
  rw [f5sheaf_scal_app]
  congr 1
  exact (CategoryTheory.congr_fun (X.presheaf.map_id _) a)

theorem f5sheaf_scalOf_comp (f g : f5sheaf_unit X ⟶ f5sheaf_unit X) :
    f5sheaf_scalOf (f ≫ g) = f5sheaf_scalOf f * f5sheaf_scalOf g := by
  rw [← f5sheaf_scal_scalOf f, ← f5sheaf_scal_scalOf g, f5sheaf_scalOf_scal, f5sheaf_scalOf_scal,
    f5sheaf_scalOf_eq]
  change (f5sheaf_scal _).val.app _ ((f5sheaf_scal _).val.app _ (1 : Γ(X, ⊤))) = _
  rw [f5sheaf_scal_top, f5sheaf_scal_top, one_mul]

theorem f5sheaf_scal_comp (a b : Γ(X, ⊤)) :
    f5sheaf_scal a ≫ f5sheaf_scal b = f5sheaf_scal (a * b) := by
  rw [← f5sheaf_scal_scalOf (f5sheaf_scal a ≫ f5sheaf_scal b), f5sheaf_scalOf_comp,
    f5sheaf_scalOf_scal, f5sheaf_scalOf_scal]

theorem f5sheaf_scal_one : f5sheaf_scal (1 : Γ(X, ⊤)) = 𝟙 _ := by
  rw [← f5sheaf_scal_scalOf (𝟙 _)]
  rfl

theorem f5sheaf_scalOf_add (f g : f5sheaf_unit X ⟶ f5sheaf_unit X) :
    f5sheaf_scalOf (f + g) = f5sheaf_scalOf f + f5sheaf_scalOf g := rfl

theorem f5sheaf_scal_add (a b : Γ(X, ⊤)) :
    f5sheaf_scal (a + b) = f5sheaf_scal a + f5sheaf_scal b := by
  rw [← f5sheaf_scal_scalOf (f5sheaf_scal a + f5sheaf_scal b), f5sheaf_scalOf_add,
    f5sheaf_scalOf_scal, f5sheaf_scalOf_scal]

theorem f5sheaf_scal_zero : f5sheaf_scal (0 : Γ(X, ⊤)) = 0 := by
  rw [← f5sheaf_scal_scalOf 0]
  rfl

theorem f5sheaf_scal_sum {ι : Type*} (s : Finset ι) (a : ι → Γ(X, ⊤)) :
    f5sheaf_scal (∑ i ∈ s, a i) = ∑ i ∈ s, f5sheaf_scal (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [f5sheaf_scal_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, f5sheaf_scal_add, ih]


/-! ### Matrices between free sheaves -/

/-- The morphism of free sheaves `𝒪^ι ⟶ 𝒪^κ` of a matrix: the `j`-th generator goes to
`∑ᵢ Y i j • eᵢ`.
Source: EGA 0_I, §5.4.1 (morphisms of free modules); Bourbaki, Algèbre, Ch. II, §10. -/
def f5sheaf_matHom {ι κ : Type} [Fintype κ] (Y : Matrix κ ι Γ(X, ⊤)) :
    f5sheaf_free X ι ⟶ f5sheaf_free X κ :=
  Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan ι)
    fun j => ∑ i, f5sheaf_scal (Y i j) ≫ f5sheaf_ιFree i

@[reassoc]
theorem f5sheaf_ιFree_matHom {ι κ : Type} [Fintype κ] (Y : Matrix κ ι Γ(X, ⊤)) (j : ι) :
    f5sheaf_ιFree j ≫ f5sheaf_matHom Y = ∑ i, f5sheaf_scal (Y i j) ≫ f5sheaf_ιFree i :=
  Cofan.IsColimit.fac _ _ _

/-- The projection of a free sheaf onto the factor of index `l`.
Source: EGA 0_I, §5.4.1. -/
def f5sheaf_freeProj {κ : Type} [DecidableEq κ] (l : κ) :
    f5sheaf_free X κ ⟶ f5sheaf_unit X :=
  Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan κ)
    fun i => (if i = l then 𝟙 _ else 0 : f5sheaf_unit X ⟶ f5sheaf_unit X)

@[reassoc]
theorem f5sheaf_ιFree_freeProj {κ : Type} [DecidableEq κ] (i l : κ) :
    f5sheaf_ιFree i ≫ (f5sheaf_freeProj l : f5sheaf_free X κ ⟶ _) =
      if i = l then 𝟙 _ else 0 :=
  Cofan.IsColimit.fac _ _ _

theorem f5sheaf_sum_freeProj {κ : Type} [Fintype κ] [DecidableEq κ] :
    ∑ l, (f5sheaf_freeProj (X := X) l ≫ f5sheaf_ιFree l) = 𝟙 (f5sheaf_free X κ) := by
  apply f5sheaf_free_hom_ext
  intro i
  rw [Preadditive.comp_sum, Category.comp_id]
  simp_rw [f5sheaf_ιFree_freeProj_assoc]
  rw [Finset.sum_eq_single i (fun l _ hl => by rw [ite_eq_right (Ne.symm hl), zero_comp])
    (fun h => absurd (Finset.mem_univ i) h), ite_eq_left rfl, Category.id_comp]

/-- The matrix of a morphism between free sheaves.
Source: EGA 0_I, §5.4.1; Bourbaki, Algèbre, Ch. II, §10. -/
def f5sheaf_matOf {ι κ : Type} [DecidableEq κ] (f : f5sheaf_free X ι ⟶ f5sheaf_free X κ) :
    Matrix κ ι Γ(X, ⊤) :=
  Matrix.of fun l j => f5sheaf_scalOf (f5sheaf_ιFree j ≫ f ≫ f5sheaf_freeProj l)

theorem f5sheaf_matHom_matOf {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (f : f5sheaf_free X ι ⟶ f5sheaf_free X κ) :
    f5sheaf_matHom (f5sheaf_matOf f) = f := by
  apply f5sheaf_free_hom_ext
  intro j
  rw [f5sheaf_ιFree_matHom]
  simp only [f5sheaf_matOf, Matrix.of_apply, f5sheaf_scal_scalOf, Category.assoc]
  rw [← Preadditive.comp_sum, ← Preadditive.comp_sum, f5sheaf_sum_freeProj, Category.comp_id]

theorem f5sheaf_matOf_matHom {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (Y : Matrix κ ι Γ(X, ⊤)) : f5sheaf_matOf (f5sheaf_matHom Y) = Y := by
  ext l j
  simp only [f5sheaf_matOf, Matrix.of_apply]
  rw [f5sheaf_ιFree_matHom_assoc, Preadditive.sum_comp]
  simp_rw [Category.assoc, f5sheaf_ιFree_freeProj]
  rw [Finset.sum_eq_single l (fun i _ hi => by rw [ite_eq_right hi, comp_zero])
    (fun h => absurd (Finset.mem_univ l) h), ite_eq_left rfl, Category.comp_id, f5sheaf_scalOf_scal]

theorem f5sheaf_matHom_injective {ι κ : Type} [Fintype κ] :
    Function.Injective (f5sheaf_matHom (X := X) (ι := ι) (κ := κ)) := by
  classical
  intro Y Z h
  rw [← f5sheaf_matOf_matHom Y, h, f5sheaf_matOf_matHom]

theorem f5sheaf_matHom_surjective {ι κ : Type} [Fintype κ]
    (f : f5sheaf_free X ι ⟶ f5sheaf_free X κ) :
    ∃ Y, f5sheaf_matHom Y = f := by
  classical
  exact ⟨_, f5sheaf_matHom_matOf f⟩

theorem f5sheaf_matHom_comp {ι κ μ : Type} [Fintype κ] [Fintype μ]
    (Y : Matrix κ ι Γ(X, ⊤)) (Z : Matrix μ κ Γ(X, ⊤)) :
    f5sheaf_matHom Y ≫ f5sheaf_matHom Z = f5sheaf_matHom (Z * Y) := by
  apply f5sheaf_free_hom_ext
  intro j
  rw [f5sheaf_ιFree_matHom_assoc, f5sheaf_ιFree_matHom, Preadditive.sum_comp]
  simp_rw [Category.assoc, f5sheaf_ιFree_matHom, Preadditive.comp_sum, ← Category.assoc,
    f5sheaf_scal_comp, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [f5sheaf_scal_sum, Preadditive.sum_comp]
  simp_rw [mul_comm]

theorem f5sheaf_matHom_one {ι : Type} [Fintype ι] [DecidableEq ι] :
    f5sheaf_matHom (1 : Matrix ι ι Γ(X, ⊤)) = 𝟙 _ := by
  apply f5sheaf_free_hom_ext
  intro j
  rw [f5sheaf_ιFree_matHom, Category.comp_id]
  rw [Finset.sum_eq_single j (fun i _ hi => by
      rw [Matrix.one_apply_ne hi, f5sheaf_scal_zero, zero_comp])
    (fun h => absurd (Finset.mem_univ j) h), Matrix.one_apply_eq, f5sheaf_scal_one,
    Category.id_comp]

/-- The automorphism of a free sheaf of an invertible matrix.
Source: EGA 0_I, §5.4.1. -/
def f5sheaf_matIso {κ : Type} [Fintype κ] [DecidableEq κ] (h : Matrix κ κ Γ(X, ⊤))
    (hu : IsUnit h.det) : f5sheaf_free X κ ≅ f5sheaf_free X κ where
  hom := f5sheaf_matHom h
  inv := f5sheaf_matHom h⁻¹
  hom_inv_id := by rw [f5sheaf_matHom_comp, Matrix.nonsing_inv_mul _ hu, f5sheaf_matHom_one]
  inv_hom_id := by rw [f5sheaf_matHom_comp, Matrix.mul_nonsing_inv _ hu, f5sheaf_matHom_one]


theorem f5sheaf_unit_hom_ext {M : X.Modules} {g h : f5sheaf_unit X ⟶ M}
    (H : ∀ U : X.Opensᵒᵖ, g.val.app U (1 : Γ(X, U.unop)) = h.val.app U (1 : Γ(X, U.unop))) :
    g = h := by
  apply (SheafOfModules.unitHomEquiv (R := X.ringCatSheaf) M).injective
  apply PresheafOfModules.sections_ext
  exact H

/-! ### Pullbacks of matrices -/

variable {X' : Scheme.{0}}

instance f5sheaf_pushforward_isRightAdjoint (f : X' ⟶ X) :
    (SheafOfModules.pushforward.{0} f.toRingCatSheafHom).IsRightAdjoint :=
  (inferInstance : (Scheme.Modules.pushforward f).IsRightAdjoint)

/-- The identification of the pullback of a free sheaf with the free sheaf, as an isomorphism in
`X'.Modules`; it is `f5_pullbackFreeIso`.
Source: Mathlib `SheafOfModules.pullbackObjFreeIso`; EGA 0_I, §4.3.2. -/
def f5sheaf_pullbackFreeIso (f : X' ⟶ X) (I : Type) :
    (Scheme.Modules.pullback f).obj (f5sheaf_free X I) ≅ f5sheaf_free X' I :=
  f5_pullbackFreeIso f I

theorem f5sheaf_pullbackFreeIso_eq (f : X' ⟶ X) (I : Type) :
    f5sheaf_pullbackFreeIso f I = f5_pullbackFreeIso f I := rfl

/-- The identification of the pullback of the unit sheaf with the unit sheaf.
Source: Mathlib `SheafOfModules.pullbackObjUnitToUnit`; EGA 0_I, §4.3.1. -/
def f5sheaf_pullbackUnit (f : X' ⟶ X) :
    (Scheme.Modules.pullback f).obj (f5sheaf_unit X) ⟶ f5sheaf_unit X' :=
  SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom

@[reassoc]
theorem f5sheaf_pullback_ιFree_freeIso (f : X' ⟶ X) {I : Type} (i : I) :
    (Scheme.Modules.pullback f).map (f5sheaf_ιFree i) ≫ (f5sheaf_pullbackFreeIso f I).hom =
      f5sheaf_pullbackUnit f ≫ f5sheaf_ιFree i :=
  SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ i

theorem f5sheaf_homEquiv_pullbackUnit (f : X' ⟶ X) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (f5sheaf_pullbackUnit f) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

theorem f5sheaf_pullback_scal (f : X' ⟶ X) (a : Γ(X, ⊤)) :
    (Scheme.Modules.pullback f).map (f5sheaf_scal a) ≫ f5sheaf_pullbackUnit f =
      f5sheaf_pullbackUnit f ≫ f5sheaf_scal (f.appTop a) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    f5sheaf_homEquiv_pullbackUnit]
  apply f5sheaf_unit_hom_ext
  intro U
  change f.app U.unop ((1 : Γ(X, U.unop)) * X.presheaf.map (homOfLE le_top).op a) =
    f.app U.unop 1 * X'.presheaf.map (homOfLE le_top).op (f.appTop a)
  rw [one_mul, map_one, one_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    f.naturality]
  rfl


/-- The matrix with entries pulled back along `f`.
Source: EGA 0_I, §4.3.1 (inverse images of sections). -/
def f5sheaf_matPullback {ι κ : Type} (f : X' ⟶ X) (Y : Matrix κ ι Γ(X, ⊤)) :
    Matrix κ ι Γ(X', ⊤) :=
  Y.map f.appTop

theorem f5sheaf_pullback_matHom (f : X' ⟶ X) {ι κ : Type} [Fintype κ] (Y : Matrix κ ι Γ(X, ⊤)) :
    (Scheme.Modules.pullback f).map (f5sheaf_matHom Y) ≫ (f5sheaf_pullbackFreeIso f κ).hom =
      (f5sheaf_pullbackFreeIso f ι).hom ≫ f5sheaf_matHom (f5sheaf_matPullback f Y) := by
  refine Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback f) _ _
    (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) ι)) _ _ (fun j => ?_)
  change (Scheme.Modules.pullback f).map (f5sheaf_ιFree j) ≫ _ =
    (Scheme.Modules.pullback f).map (f5sheaf_ιFree j) ≫ _
  rw [← Category.assoc, ← Functor.map_comp, f5sheaf_ιFree_matHom,
    f5sheaf_pullback_ιFree_freeIso_assoc, f5sheaf_ιFree_matHom, Functor.map_sum,
    Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Functor.map_comp, Category.assoc, f5sheaf_pullback_ιFree_freeIso, ← Category.assoc,
    f5sheaf_pullback_scal, Category.assoc]
  rfl

end HodgeLean.Foundations.Algebraic
