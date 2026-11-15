import HodgeLean.Foundations.Algebraic.GrassmannianSheafRestrict

/-! # Grassmannian sheaf lane: pullbacks of quotients of free sheaves

For a morphism of schemes `f : X' ⟶ X` and a morphism `ψ : 𝒪^I ⟶ F` of sheaves of modules on
`X`, the pulled-back morphism `f5sheaf_pb f ψ : 𝒪^I ⟶ f^* F` is the pullback of `ψ` preceded by
the identification `𝒪^I ≅ f^* 𝒪^I`. Up to isomorphism of quotients:

* the pullback of the morphism of a matrix is the morphism of the pulled-back matrix;
* pulling back along `f' ≫ f` is pulling back along `f` and then along `f'`;
* along an open immersion, pulling back is restricting.

The last two rest on the compatibility of the identifications `f^* 𝒪 ≅ 𝒪` with composition and
with restriction, which follows from the adjunctions: a morphism out of `𝒪` is determined by the
image of the section `1`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace HodgeLean.Foundations.Algebraic

set_option backward.isDefEq.respectTransparency false

variable {X X' X'' : Scheme.{0}}

/-! ### Adjunctions and conjugates -/

theorem f5sheaf_homEquiv_conj {C D : Type*} [Category C] [Category D] {L₁ L₂ : C ⥤ D}
    {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) (c : C) (d : D)
    (h : L₁.obj c ⟶ d) :
    adj₂.homEquiv c d (α.app c ≫ h) =
      adj₁.homEquiv c d h ≫ (conjugateEquiv adj₁ adj₂ α).app d := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv, Category.assoc, Category.assoc, (conjugateEquiv adj₁ adj₂ α).naturality]

/-! ### The identification of pullbacks of the unit sheaf -/

theorem f5sheaf_pullbackComp_unit (f' : X'' ⟶ X') (f : X' ⟶ X) :
    (Scheme.Modules.pullbackComp f' f).hom.app (f5sheaf_unit X) ≫
        f5sheaf_pullbackUnit (f' ≫ f) =
      (Scheme.Modules.pullback f').map (f5sheaf_pullbackUnit f) ≫ f5sheaf_pullbackUnit f' := by
  rw [← cancel_epi ((Scheme.Modules.pullbackComp f' f).inv.app _), Iso.inv_hom_id_app_assoc]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f' ≫ f)).homEquiv _ _).injective
  rw [f5sheaf_homEquiv_pullbackUnit, f5sheaf_homEquiv_conj,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv]
  have hc : ∀ h, ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f')).homEquiv
        (f5sheaf_unit X) (f5sheaf_unit X'') h =
      (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        ((Scheme.Modules.pullbackPushforwardAdjunction f').homEquiv _ _ h) := fun h => by
    rw [Adjunction.comp_homEquiv]; rfl
  rw [hc, Adjunction.homEquiv_naturality_left, f5sheaf_homEquiv_pullbackUnit,
    Adjunction.homEquiv_naturality_right, f5sheaf_homEquiv_pullbackUnit]
  apply f5sheaf_unit_hom_ext
  intro U
  change (f' ≫ f).app U.unop (1 : Γ(X, U.unop)) = f'.app _ (f.app U.unop (1 : Γ(X, U.unop)))
  rw [map_one, map_one, map_one]


theorem f5sheaf_restrictIsoPullback_unit (j : X' ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctorIsoPullback j).hom.app (f5sheaf_unit X) ≫
        f5sheaf_pullbackUnit j =
      (Scheme.Modules.restrictUnitIso j).hom := by
  apply ((Scheme.Modules.restrictAdjunction j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Scheme.Modules.restrictFunctorIsoPullback,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit,
    f5sheaf_homEquiv_pullbackUnit, Adjunction.homEquiv_unit]
  apply f5sheaf_unit_hom_ext
  intro U
  change j.app U.unop (1 : Γ(X, U.unop)) =
    (j.appIso (j ⁻¹ᵁ U.unop)).hom (X.presheaf.map _ (1 : Γ(X, U.unop)))
  rw [map_one, map_one, map_one]

/-! ### The identification of pullbacks of free sheaves -/

theorem f5sheaf_pullbackComp_free (f' : X'' ⟶ X') (f : X' ⟶ X) (I : Type) :
    (Scheme.Modules.pullbackComp f' f).hom.app (f5sheaf_free X I) ≫
        (f5sheaf_pullbackFreeIso (f' ≫ f) I).hom =
      (Scheme.Modules.pullback f').map (f5sheaf_pullbackFreeIso f I).hom ≫
        (f5sheaf_pullbackFreeIso f' I).hom := by
  refine Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit
    (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback f') _ _
    (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I)) _ _ (fun i => ?_)
  change (Scheme.Modules.pullback f').map ((Scheme.Modules.pullback f).map
    (f5sheaf_ιFree i)) ≫ _ = (Scheme.Modules.pullback f').map
      ((Scheme.Modules.pullback f).map (f5sheaf_ιFree i)) ≫ _
  rw [← Category.assoc, ← Functor.comp_map,
    (Scheme.Modules.pullbackComp f' f).hom.naturality, Category.assoc,
    f5sheaf_pullback_ιFree_freeIso, ← Category.assoc, f5sheaf_pullbackComp_unit,
    Functor.comp_map]
  have h1 := congrArg (Scheme.Modules.pullback f').map (f5sheaf_pullback_ιFree_freeIso f i)
  rw [Functor.map_comp, Functor.map_comp] at h1
  rw [← Category.assoc ((Scheme.Modules.pullback f').map _), h1, Category.assoc,
    Category.assoc, f5sheaf_pullback_ιFree_freeIso]

theorem f5sheaf_restrictIsoPullback_free (j : X' ⟶ X) [IsOpenImmersion j] (I : Type) :
    (f5sheaf_restrictFreeIso j I).hom ≫
        (Scheme.Modules.restrictFunctorIsoPullback j).hom.app (f5sheaf_free X I) ≫
          (f5sheaf_pullbackFreeIso j I).hom = 𝟙 _ := by
  apply f5sheaf_free_hom_ext
  intro i
  rw [f5sheaf_ιFree_restrictFreeIso_hom_assoc, ← Category.assoc
    ((Scheme.Modules.restrictFunctor j).map _), (Scheme.Modules.restrictFunctorIsoPullback j).hom.naturality,
    Category.assoc, f5sheaf_pullback_ιFree_freeIso, ← Category.assoc, ← Category.assoc,
    Category.assoc _ _ (f5sheaf_pullbackUnit j), f5sheaf_restrictIsoPullback_unit,
    Iso.inv_hom_id, Category.id_comp, Category.comp_id]


/-! ### Pulled-back and restricted quotients -/

/-- The pullback of a morphism out of a free sheaf, as a morphism out of the free sheaf.
Source: EGA 0_I, §4.3.1 (inverse images of `𝒪`-modules); Stacks Project, Tag 01AJ. -/
def f5sheaf_pb (f : X' ⟶ X) {I : Type} {F : X.Modules}
    (ψ : f5sheaf_free X I ⟶ F) :
    f5sheaf_free X' I ⟶ (Scheme.Modules.pullback f).obj F :=
  (f5sheaf_pullbackFreeIso f I).inv ≫ (Scheme.Modules.pullback f).map ψ

/-- The restriction of a morphism out of a free sheaf to an open, as a morphism out of the free
sheaf.
Source: EGA 0_I, §4.1.7 (restriction to an open). -/
def f5sheaf_rs (j : X' ⟶ X) [IsOpenImmersion j] {I : Type} {F : X.Modules}
    (ψ : f5sheaf_free X I ⟶ F) :
    f5sheaf_free X' I ⟶ (Scheme.Modules.restrictFunctor j).obj F :=
  (f5sheaf_restrictFreeIso j I).hom ≫ (Scheme.Modules.restrictFunctor j).map ψ

theorem f5sheaf_QuotIso.pb (f : X' ⟶ X) {I : Type} {F F' : X.Modules}
    {ψ : f5sheaf_free X I ⟶ F} {ψ' : f5sheaf_free X I ⟶ F'}
    (h : f5sheaf_QuotIso ψ ψ') : f5sheaf_QuotIso (f5sheaf_pb f ψ) (f5sheaf_pb f ψ') :=
  (h.map _).comp_left _

theorem f5sheaf_QuotIso.rs (j : X' ⟶ X) [IsOpenImmersion j] {I : Type} {F F' : X.Modules}
    {ψ : f5sheaf_free X I ⟶ F} {ψ' : f5sheaf_free X I ⟶ F'}
    (h : f5sheaf_QuotIso ψ ψ') : f5sheaf_QuotIso (f5sheaf_rs j ψ) (f5sheaf_rs j ψ') :=
  (h.map _).comp_left _

theorem f5sheaf_pb_matHom (f : X' ⟶ X) {ι κ : Type} [Fintype κ] (Y : Matrix κ ι Γ(X, ⊤)) :
    f5sheaf_QuotIso (f5sheaf_pb f (f5sheaf_matHom Y)) (f5sheaf_matHom (f5sheaf_matPullback f Y)) :=
  ⟨f5sheaf_pullbackFreeIso f κ, by
    rw [f5sheaf_pb, Category.assoc, f5sheaf_pullback_matHom, Iso.inv_hom_id_assoc]⟩

theorem f5sheaf_rs_matHom (j : X' ⟶ X) [IsOpenImmersion j] {ι κ : Type} [Fintype κ]
    (Y : Matrix κ ι Γ(X, ⊤)) :
    f5sheaf_QuotIso (f5sheaf_rs j (f5sheaf_matHom Y)) (f5sheaf_matHom (f5sheaf_matPullback j Y)) :=
  ⟨(f5sheaf_restrictFreeIso j κ).symm, by
    have h := f5sheaf_restrict_matHom j Y
    rw [f5sheaf_rs, Category.assoc, Iso.symm_hom]
    rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩

theorem f5sheaf_pb_comp (f' : X'' ⟶ X') (f : X' ⟶ X) {I : Type} {F : X.Modules}
    (ψ : f5sheaf_free X I ⟶ F) :
    f5sheaf_QuotIso (f5sheaf_pb (f' ≫ f) ψ) (f5sheaf_pb f' (f5sheaf_pb f ψ)) := by
  refine ⟨((Scheme.Modules.pullbackComp f' f).app F).symm, ?_⟩
  have h := f5sheaf_pullbackComp_free f' f I
  have h' : (f5sheaf_pullbackFreeIso (f' ≫ f) I).inv ≫
      (Scheme.Modules.pullbackComp f' f).inv.app (f5sheaf_free X I) =
      (f5sheaf_pullbackFreeIso f' I).inv ≫
        (Scheme.Modules.pullback f').map (f5sheaf_pullbackFreeIso f I).inv := by
    exact congrArg Iso.inv (Iso.ext h : ((Scheme.Modules.pullbackComp f' f).app _ ≪≫
      f5sheaf_pullbackFreeIso (f' ≫ f) I) =
        (Scheme.Modules.pullback f').mapIso (f5sheaf_pullbackFreeIso f I) ≪≫
          f5sheaf_pullbackFreeIso f' I)
  have nat := (Scheme.Modules.pullbackComp f' f).inv.naturality ψ
  rw [Iso.symm_hom, Iso.app_inv, f5sheaf_pb, f5sheaf_pb, f5sheaf_pb, Category.assoc, nat,
    ← Category.assoc, h', Category.assoc, Functor.comp_map, Functor.map_comp]

theorem f5sheaf_rs_pb (j : X' ⟶ X) [IsOpenImmersion j] {I : Type} {F : X.Modules}
    (ψ : f5sheaf_free X I ⟶ F) :
    f5sheaf_QuotIso (f5sheaf_rs j ψ) (f5sheaf_pb j ψ) := by
  refine ⟨(Scheme.Modules.restrictFunctorIsoPullback j).app F, ?_⟩
  have h := f5sheaf_restrictIsoPullback_free j I
  have h' : (f5sheaf_restrictFreeIso j I).hom ≫
      (Scheme.Modules.restrictFunctorIsoPullback j).hom.app (f5sheaf_free X I) =
      (f5sheaf_pullbackFreeIso j I).inv := by
    rw [← Iso.comp_hom_eq_id, Category.assoc]
    exact h
  rw [Iso.app_hom, f5sheaf_rs, f5sheaf_pb, Category.assoc,
    (Scheme.Modules.restrictFunctorIsoPullback j).hom.naturality, ← Category.assoc, h']

end HodgeLean.Foundations.Algebraic
