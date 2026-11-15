import HodgeLean.Foundations.Algebraic.GrassmannianSheafFree

/-! # Grassmannian sheaf lane: quotients of sheaves of modules, checked locally

Two morphisms `q : M ⟶ F` and `q' : M ⟶ F'` of sheaves of modules are isomorphic quotients of
`M` (`f5sheaf_QuotIso`) when `q' = q ≫ e` for an isomorphism `e : F ≅ F'`. Two epimorphisms are
isomorphic quotients as soon as each kills the kernel of the other. A morphism of sheaves of
modules on a scheme vanishes when its restrictions to the members of an open cover vanish; hence
two epimorphisms that are isomorphic quotients on each member of an open cover are isomorphic
quotients.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace HodgeLean.Foundations.Algebraic

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}}

/-! ### Isomorphic quotients -/

/-- Two morphisms out of `M` are isomorphic quotients of `M`: they differ by an isomorphism of
their targets.
Source: EGA 0_I, §4.1.5; Stacks Project, Tag 01AF (quotient modules). -/
def f5sheaf_QuotIso {M F F' : X.Modules} (q : M ⟶ F) (q' : M ⟶ F') : Prop :=
  ∃ e : F ≅ F', q ≫ e.hom = q'

theorem f5sheaf_QuotIso.refl {M F : X.Modules} (q : M ⟶ F) : f5sheaf_QuotIso q q :=
  ⟨Iso.refl _, Category.comp_id _⟩

theorem f5sheaf_QuotIso.symm {M F F' : X.Modules} {q : M ⟶ F} {q' : M ⟶ F'}
    (h : f5sheaf_QuotIso q q') : f5sheaf_QuotIso q' q := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, by rw [← he, Category.assoc, Iso.symm_hom, e.hom_inv_id, Category.comp_id]⟩

theorem f5sheaf_QuotIso.trans {M F F' F'' : X.Modules} {q : M ⟶ F} {q' : M ⟶ F'}
    {q'' : M ⟶ F''} (h : f5sheaf_QuotIso q q') (h' : f5sheaf_QuotIso q' q'') :
    f5sheaf_QuotIso q q'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e ≪≫ e', by rw [Iso.trans_hom, ← Category.assoc, he, he']⟩

theorem f5sheaf_QuotIso.of_iso {M F F' : X.Modules} (q : M ⟶ F) (e : F ≅ F') :
    f5sheaf_QuotIso q (q ≫ e.hom) :=
  ⟨e, rfl⟩

theorem f5sheaf_QuotIso.comp_left {M M' F F' : X.Modules} (ρ : M' ⟶ M) {q : M ⟶ F}
    {q' : M ⟶ F'} (h : f5sheaf_QuotIso q q') : f5sheaf_QuotIso (ρ ≫ q) (ρ ≫ q') := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, by rw [Category.assoc, he]⟩

theorem f5sheaf_QuotIso.cancel_left {M M' F F' : X.Modules} (ρ : M' ⟶ M) [IsIso ρ]
    {q : M ⟶ F} {q' : M ⟶ F'} (h : f5sheaf_QuotIso (ρ ≫ q) (ρ ≫ q')) :
    f5sheaf_QuotIso q q' := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, by rw [← cancel_epi ρ, ← Category.assoc, he]⟩

theorem f5sheaf_QuotIso.map {Y : Scheme.{0}} (G : X.Modules ⥤ Y.Modules) {M F F' : X.Modules}
    {q : M ⟶ F} {q' : M ⟶ F'} (h : f5sheaf_QuotIso q q') :
    f5sheaf_QuotIso (G.map q) (G.map q') := by
  obtain ⟨e, he⟩ := h
  exact ⟨G.mapIso e, by rw [Functor.mapIso_hom, ← Functor.map_comp, he]⟩

/-- Two epimorphisms each killing the kernel of the other are isomorphic quotients. -/
theorem f5sheaf_QuotIso.of_kernel {M F F' : X.Modules} (q : M ⟶ F) (q' : M ⟶ F') [Epi q]
    [Epi q'] (h : kernel.ι q ≫ q' = 0) (h' : kernel.ι q' ≫ q = 0) : f5sheaf_QuotIso q q' := by
  let c := Abelian.epiIsCokernelOfKernel _ (kernelIsKernel q)
  let c' := Abelian.epiIsCokernelOfKernel _ (kernelIsKernel q')
  let a : F ⟶ F' := c.desc (CokernelCofork.ofπ q' h)
  let b : F' ⟶ F := c'.desc (CokernelCofork.ofπ q h')
  have ha : q ≫ a = q' := c.fac (CokernelCofork.ofπ q' h) WalkingParallelPair.one
  have hb : q' ≫ b = q := c'.fac (CokernelCofork.ofπ q h') WalkingParallelPair.one
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · rw [← cancel_epi q, ← Category.assoc, ha, hb, Category.comp_id]
  · rw [← cancel_epi q', ← Category.assoc, hb, ha, Category.comp_id]


/-! ### Checking on an open cover -/

theorem f5sheaf_hom_naturality_apply {M N : X.Modules} (f : M ⟶ N) {V W : X.Opens}
    (i : W ⟶ V) (s : Γ(M, V)) :
    N.presheaf.map i.op (f.app V s) = f.app W (M.presheaf.map i.op s) :=
  (ConcreteCategory.congr_hom (f.mapPresheaf.naturality i.op) s).symm

/-- Morphisms of sheaves of modules agreeing on the members of an open cover agree. -/
theorem f5sheaf_hom_ext_of_restrict {M N : X.Modules} {f g : M ⟶ N} {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (h : ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).map f =
      (Scheme.Modules.restrictFunctor (U i).ι).map g) : f = g := by
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  let NS : TopCat.Sheaf AddCommGrpCat X := ⟨N.presheaf, N.isSheaf⟩
  refine NS.eq_of_locally_eq' (U := fun i => (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ V)) V
    (fun i => homOfLE ((U i).ι.image_preimage_le V)) ?_ _ _ (fun i => ?_)
  · intro x hx
    obtain ⟨i, hi⟩ := hU x
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact ⟨hi, hx⟩
  · change N.presheaf.map _ (f.app V s) = N.presheaf.map _ (g.app V s)
    rw [f5sheaf_hom_naturality_apply, f5sheaf_hom_naturality_apply]
    change ((Scheme.Modules.restrictFunctor (U i).ι).map f).app ((U i).ι ⁻¹ᵁ V) _ =
      ((Scheme.Modules.restrictFunctor (U i).ι).map g).app ((U i).ι ⁻¹ᵁ V) _
    rw [h i]


instance f5sheaf_restrict_preservesZero (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

theorem f5sheaf_eq_zero_of_restrict {M N : X.Modules} {f : M ⟶ N} {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (h : ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).map f = 0) : f = 0 :=
  f5sheaf_hom_ext_of_restrict U hU fun i => by rw [h i, Functor.map_zero]

/-- Two epimorphisms that are isomorphic quotients on each member of an open cover are isomorphic
quotients. -/
theorem f5sheaf_QuotIso.of_restrict {M F F' : X.Modules} (q : M ⟶ F) (q' : M ⟶ F') [Epi q]
    [Epi q'] {ι : Type*} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (h : ∀ i, f5sheaf_QuotIso ((Scheme.Modules.restrictFunctor (U i).ι).map q)
      ((Scheme.Modules.restrictFunctor (U i).ι).map q')) : f5sheaf_QuotIso q q' := by
  refine f5sheaf_QuotIso.of_kernel q q' (f5sheaf_eq_zero_of_restrict U hU fun i => ?_)
    (f5sheaf_eq_zero_of_restrict U hU fun i => ?_)
  · obtain ⟨e, he⟩ := h i
    rw [Functor.map_comp, ← he, ← Category.assoc, ← Functor.map_comp, kernel.condition,
      Functor.map_zero, zero_comp]
  · obtain ⟨e, he⟩ := (h i).symm
    rw [Functor.map_comp, ← he, ← Category.assoc, ← Functor.map_comp, kernel.condition,
      Functor.map_zero, zero_comp]

end HodgeLean.Foundations.Algebraic
