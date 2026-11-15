import HodgeLean.Foundations.Algebraic.GrassmannianSheafRestrict

/-! # Grassmannian sheaf lane: gluing quotients along an open cover

Let `M` be a sheaf of modules on a scheme `X`, `U i` an open cover of `X`, and
`q i : M|_{U i} ⟶ F i` epimorphisms. Say that `q i` kills a section `s` of `M` over `V` when it
kills the restriction of `s` to `V ∩ U i`. If, over every open `V ⊆ U j`, every section killed by
`q j` is killed by `q i`, then the quotients glue: the cokernel `π : M ⟶ Q` of the kernel of
`M ⟶ ∏ᵢ (U i)_* F i` restricts on each `U i` to a quotient isomorphic to `q i`.

The proof uses that restriction to an open is exact: it preserves the cokernel defining `π`, and
the kernel and product defining the kernel of `M ⟶ ∏ᵢ (U i)_* F i`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace HodgeLean.Foundations.Algebraic

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} {ι : Type} (U : ι → X.Opens) {M : X.Modules}
  {F : ∀ i, (U i).toScheme.Modules} (q : ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).obj M ⟶ F i)

/-- The morphism `q i` kills the section `s` of `M` over `V`: it kills its restriction to
`V ∩ U i`.
Source: EGA 0_I, §3.3.1 (gluing sheaves); Stacks Project, Tag 00AK. -/
def f5sheaf_Kills (i : ι) (V : X.Opens) (s : Γ(M, V)) : Prop :=
  (q i).app ((U i).ι ⁻¹ᵁ V) (M.presheaf.map (homOfLE ((U i).ι.image_preimage_le V)).op s) = 0

/-- The compatibility of the local quotients: over an open `V ⊆ U j`, a section killed by `q j` is
killed by `q i`.
Source: EGA 0_I, §3.3.1; Stacks Project, Tag 00AK. -/
def f5sheaf_KillsCompat : Prop :=
  ∀ i j (V : X.Opens), V ≤ U j → ∀ s : Γ(M, V), f5sheaf_Kills U q j V s → f5sheaf_Kills U q i V s

/-- The morphism of `M` into the product of the pushforwards of the targets of the `q i`.
Source: EGA 0_I, §3.3.1. -/
def f5sheaf_glueMap : M ⟶ ∏ᶜ fun i => (Scheme.Modules.pushforward (U i).ι).obj (F i) :=
  Pi.lift fun i => (Scheme.Modules.restrictAdjunction (U i).ι).homEquiv _ _ (q i)

/-- The glued quotient: the cokernel of the kernel of `f5sheaf_glueMap`.
Source: EGA 0_I, §3.3.1; Stacks Project, Tag 00AK. -/
def f5sheaf_glueQuot : X.Modules :=
  cokernel (kernel.ι (f5sheaf_glueMap U q))

/-- The glued quotient morphism.
Source: EGA 0_I, §3.3.1; Stacks Project, Tag 00AK. -/
def f5sheaf_glueπ : M ⟶ f5sheaf_glueQuot U q :=
  cokernel.π (kernel.ι (f5sheaf_glueMap U q))

instance : Epi (f5sheaf_glueπ U q) := by
  dsimp [f5sheaf_glueπ]; infer_instance

theorem f5sheaf_glueMap_π (i : ι) :
    f5sheaf_glueMap U q ≫ Pi.π _ i =
      (Scheme.Modules.restrictAdjunction (U i).ι).homEquiv _ _ (q i) := by
  simp [f5sheaf_glueMap]

theorem f5sheaf_q_eq (i : ι) :
    q i = (Scheme.Modules.restrictFunctor (U i).ι).map (f5sheaf_glueMap U q ≫ Pi.π _ i) ≫
      (Scheme.Modules.restrictAdjunction (U i).ι).counit.app (F i) := by
  rw [f5sheaf_glueMap_π]
  have := (Scheme.Modules.restrictAdjunction (U i).ι).homEquiv_counit
    (g := (Scheme.Modules.restrictAdjunction (U i).ι).homEquiv _ _ (q i))
  rw [Equiv.symm_apply_apply] at this
  exact this

theorem f5sheaf_kernel_restrict_q (i : ι) :
    (Scheme.Modules.restrictFunctor (U i).ι).map (kernel.ι (f5sheaf_glueMap U q)) ≫ q i = 0 := by
  rw [f5sheaf_q_eq U q i, ← Category.assoc, ← Functor.map_comp, ← Category.assoc,
    kernel.condition, zero_comp, Functor.map_zero, zero_comp]


theorem f5sheaf_homEquiv_app (i : ι) (V : X.Opens) (t : Γ(M, V)) :
    ((Scheme.Modules.restrictAdjunction (U i).ι).homEquiv _ _ (q i)).app V t =
      (q i).app ((U i).ι ⁻¹ᵁ V)
        (M.presheaf.map (homOfLE ((U i).ι.image_preimage_le V)).op t) := by
  rw [Adjunction.homEquiv_unit]
  rfl

theorem f5sheaf_kills_of_app (j : ι) (W : (U j).toScheme.Opens) (t : Γ(M, (U j).ι ''ᵁ W))
    (h : (q j).app W t = 0) : f5sheaf_Kills U q j ((U j).ι ''ᵁ W) t := by
  have hW : (U j).ι ⁻¹ᵁ ((U j).ι ''ᵁ W) = W := (U j).ι.preimage_image_eq W
  have key := f5sheaf_hom_naturality_apply (q j) (homOfLE hW.le) t
  rw [h, map_zero] at key
  exact key.symm

theorem f5sheaf_kernel_comp_homEquiv [∀ i, Epi (q i)] (hc : f5sheaf_KillsCompat U q)
    (i j : ι) :
    kernel.ι (q j) ≫ (Scheme.Modules.restrictFunctor (U j).ι).map
      ((Scheme.Modules.restrictAdjunction (U i).ι).homEquiv _ _ (q i)) = 0 := by
  apply Scheme.Modules.hom_ext
  intro W
  ext x
  have h0 : (q j).app W ((kernel.ι (q j)).app W x) = 0 := by
    have := ConcreteCategory.congr_hom
      (congrArg (fun f => Scheme.Modules.Hom.app f W) (kernel.condition (q j))) x
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app,
      ConcreteCategory.comp_apply] at this
    exact this.trans rfl
  have hk := hc i j _ ((U j).ι.image_le_opensRange W |>.trans_eq (U j).opensRange_ι) _
    (f5sheaf_kills_of_app U q j W _ h0)
  change ((Scheme.Modules.restrictAdjunction (U i).ι).homEquiv _ _ (q i)).app ((U j).ι ''ᵁ W)
    ((kernel.ι (q j)).app W x) = 0
  rw [f5sheaf_homEquiv_app]
  exact hk


/-- Gluing of quotients: on each member of the cover, the glued quotient restricts to a quotient
isomorphic to the given one. -/
theorem f5sheaf_glue_quotIso [∀ i, Epi (q i)] (hc : f5sheaf_KillsCompat U q) (j : ι) :
    f5sheaf_QuotIso ((Scheme.Modules.restrictFunctor (U j).ι).map (f5sheaf_glueπ U q)) (q j) := by
  let R := Scheme.Modules.restrictFunctor (U j).ι
  let Φ := f5sheaf_glueMap U q
  refine f5sheaf_QuotIso.of_kernel _ _ ?_ ?_
  · have hc' := CokernelCofork.mapIsColimit _ (cokernelIsCokernel (kernel.ι Φ)) R
    obtain ⟨t, ht⟩ := CokernelCofork.IsColimit.desc' hc' (q j) (f5sheaf_kernel_restrict_q U q j)
    change R.map (f5sheaf_glueπ U q) ≫ t = q j at ht
    rw [← ht, ← Category.assoc, kernel.condition, zero_comp]
  · have hl := KernelFork.mapIsLimit _ (kernelIsKernel Φ) R
    have h2 : kernel.ι (q j) ≫ R.map Φ = 0 := by
      rw [← cancel_mono (piComparison R fun i => (Scheme.Modules.pushforward (U i).ι).obj (F i))]
      refine Pi.hom_ext _ _ fun i => ?_
      rw [Category.assoc, Category.assoc, piComparison_comp_π, ← R.map_comp, f5sheaf_glueMap_π,
        f5sheaf_kernel_comp_homEquiv U q hc i j, zero_comp, zero_comp]
    obtain ⟨l, hl'⟩ := KernelFork.IsLimit.lift' hl (kernel.ι (q j)) h2
    change l ≫ R.map (kernel.ι Φ) = kernel.ι (q j) at hl'
    rw [← hl', Category.assoc, ← R.map_comp]
    change l ≫ R.map (kernel.ι Φ ≫ cokernel.π (kernel.ι Φ)) = 0
    rw [cokernel.condition, R.map_zero, comp_zero]


/-! ### Compatibility from isomorphic quotients on overlaps -/

theorem f5sheaf_map_map {Y : Scheme.{0}} (P : Y.Modules) {A B C : Y.Opens} (f : B ⟶ A)
    (g : C ⟶ B) (h : C ⟶ A) (s : Γ(P, A)) :
    P.presheaf.map g.op (P.presheaf.map f.op s) = P.presheaf.map h.op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction to a smaller open `W ≤ V` factors through restriction to `V`.
Source: EGA 0_I, §3.2.2 (restriction to opens is transitive). -/
def f5sheaf_restrictNest {V W : X.Opens} (h : W ≤ V) :
    Scheme.Modules.restrictFunctor W.ι ≅
      Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.restrictFunctor (X.homOfLE h) :=
  Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm ≪≫
    Scheme.Modules.restrictFunctorComp (X.homOfLE h) V.ι

theorem f5sheaf_restrictNest_app {V W : X.Opens} (h : W ≤ V) (N : X.Modules)
    (O : W.toScheme.Opens) (x : Γ(N, W.ι ''ᵁ O)) :
    ((f5sheaf_restrictNest h).hom.app N).app O x =
      N.presheaf.map (homOfLE (show V.ι ''ᵁ (X.homOfLE h ''ᵁ O) ≤ W.ι ''ᵁ O by
        rw [← Scheme.Hom.comp_image]; simp only [Scheme.homOfLE_ι, le_refl])).op x := by
  simp only [f5sheaf_restrictNest, Iso.trans_hom, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app, ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The restriction of `q i` to the open `W ≤ U i`, as a morphism out of the restriction of `M`.
Source: EGA 0_I, §3.2.2. -/
def f5sheaf_restrictQ (i : ι) {W : X.Opens} (h : W ≤ U i) :
    (Scheme.Modules.restrictFunctor W.ι).obj M ⟶
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).obj (F i) :=
  (f5sheaf_restrictNest h).hom.app M ≫ (Scheme.Modules.restrictFunctor (X.homOfLE h)).map (q i)

theorem f5sheaf_restrictQ_app (i : ι) {W : X.Opens} (h : W ≤ U i) (O : W.toScheme.Opens)
    (x : Γ(M, W.ι ''ᵁ O)) :
    (f5sheaf_restrictQ U q i h).app O x =
      (q i).app (X.homOfLE h ''ᵁ O) (M.presheaf.map (homOfLE
        (show (U i).ι ''ᵁ (X.homOfLE h ''ᵁ O) ≤ W.ι ''ᵁ O by
          rw [← Scheme.Hom.comp_image]; simp only [Scheme.homOfLE_ι, le_refl])).op x) := by
  rw [f5sheaf_restrictQ, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    f5sheaf_restrictNest_app]
  rfl

/-- If the restrictions of `q i` and `q j` to `U i ⊓ U j` are isomorphic quotients for all `i, j`,
the local quotients are compatible. -/
theorem f5sheaf_killsCompat_of_quotIso
    (h : ∀ i j, f5sheaf_QuotIso (f5sheaf_restrictQ U q i (inf_le_left : U i ⊓ U j ≤ U i))
      (f5sheaf_restrictQ U q j (inf_le_right : U i ⊓ U j ≤ U j))) :
    f5sheaf_KillsCompat U q := by
  intro i j V hVj s hj
  obtain ⟨e, he⟩ := (h i j).symm
  set W := U i ⊓ U j
  set O : W.toScheme.Opens := W.ι ⁻¹ᵁ V
  have hO : W.ι ''ᵁ O ≤ V := W.ι.image_preimage_le V
  set t : Γ(M, W.ι ''ᵁ O) := M.presheaf.map (homOfLE hO).op s
  have hWO : W.ι ''ᵁ O = W ⊓ V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hc : ∀ k (hk : W ≤ U k), (U k).ι ''ᵁ (X.homOfLE hk ''ᵁ O) = W ⊓ V := by
    intro k hk
    rw [← Scheme.Hom.comp_image]; simp only [Scheme.homOfLE_ι]; exact hWO
  have h1 : (f5sheaf_restrictQ U q j (inf_le_right : W ≤ U j)).app O t = 0 := by
    have hle : X.homOfLE (inf_le_right : W ≤ U j) ''ᵁ O ≤ (U j).ι ⁻¹ᵁ V := by
      rw [← Scheme.Hom.image_le_image_iff (U j).ι, hc,
        Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have key := f5sheaf_hom_naturality_apply (q j) (homOfLE hle)
      (M.presheaf.map (homOfLE ((U j).ι.image_preimage_le V)).op s)
    rw [hj, map_zero] at key
    rw [f5sheaf_restrictQ_app, key, Scheme.Modules.restrict_map]
    simp only [t]
    have hfin : (U j).ι ''ᵁ (X.homOfLE (inf_le_right : W ≤ U j) ''ᵁ O) ≤ V := by
      rw [hc]; exact inf_le_right
    congr 1
    exact (f5sheaf_map_map M _ _ (homOfLE hfin) s).trans
      (f5sheaf_map_map M _ _ (homOfLE hfin) s).symm
  have h2 : (f5sheaf_restrictQ U q i (inf_le_left : W ≤ U i)).app O t = 0 := by
    rw [← he, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, h1, map_zero]
  have hle : (U i).ι ⁻¹ᵁ V ≤ X.homOfLE (inf_le_left : W ≤ U i) ''ᵁ O := by
    rw [← Scheme.Hom.image_le_image_iff (U i).ι, hc,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact le_inf (le_inf inf_le_left (inf_le_right.trans hVj)) inf_le_right
  rw [f5sheaf_restrictQ_app] at h2
  have hfin : (U i).ι ''ᵁ (X.homOfLE (inf_le_left : W ≤ U i) ''ᵁ O) ≤ W.ι ''ᵁ O := by
    rw [hc, hWO]
  have key := f5sheaf_hom_naturality_apply (q i) (homOfLE hle)
    (M.presheaf.map (homOfLE hfin).op t)
  rw [h2, map_zero, Scheme.Modules.restrict_map] at key
  simp only [t] at key
  unfold f5sheaf_Kills
  rw [key]
  congr 1
  have e1 := f5sheaf_map_map M (homOfLE hO) (homOfLE hfin) (homOfLE (hfin.trans hO)) s
  have e2 := f5sheaf_map_map M (homOfLE (hfin.trans hO)) ((Scheme.Hom.opensFunctor (U i).ι).map
    (homOfLE hle)) (homOfLE ((U i).ι.image_preimage_le V)) s
  exact (e1 ▸ e2).symm


/-! ### Nested restrictions of free sheaves and matrices -/

theorem f5sheaf_restrictNest_unit {V W : X.Opens} (h : W ≤ V) :
    (Scheme.Modules.restrictUnitIso W.ι).inv ≫
        (f5sheaf_restrictNest h).hom.app (f5sheaf_unit X) ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
            (Scheme.Modules.restrictUnitIso V.ι).hom =
      (Scheme.Modules.restrictUnitIso (X.homOfLE h)).inv := by
  apply f5sheaf_unit_hom_ext
  intro O
  change (V.ι.appIso (X.homOfLE h ''ᵁ O.unop)).hom (X.presheaf.map _ (X.presheaf.map _
    ((W.ι.appIso O.unop).inv (1 : Γ(W, O.unop))))) =
    ((X.homOfLE h).appIso O.unop).inv (1 : Γ(W, O.unop))
  rw [map_one, map_one, map_one, map_one, map_one]

theorem f5sheaf_restrictNest_free {V W : X.Opens} (h : W ≤ V) (I : Type) :
    (f5sheaf_restrictFreeIso W.ι I).hom ≫
        (f5sheaf_restrictNest h).hom.app (f5sheaf_free X I) ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
            (f5sheaf_restrictFreeIso V.ι I).inv =
      (f5sheaf_restrictFreeIso (X.homOfLE h) I).hom := by
  apply f5sheaf_free_hom_ext
  intro i
  have hV : (Scheme.Modules.restrictFunctor V.ι).map (f5sheaf_ιFree i) ≫
      (f5sheaf_restrictFreeIso V.ι I).inv =
      (Scheme.Modules.restrictUnitIso V.ι).hom ≫ f5sheaf_ιFree i := by
    rw [Iso.comp_inv_eq, Category.assoc, f5sheaf_ιFree_restrictFreeIso_hom,
      Iso.hom_inv_id_assoc]
  rw [f5sheaf_ιFree_restrictFreeIso_hom_assoc, f5sheaf_ιFree_restrictFreeIso_hom,
    ← Category.assoc ((Scheme.Modules.restrictFunctor W.ι).map _),
    (f5sheaf_restrictNest h).hom.naturality, Category.assoc, Functor.comp_map,
    ← Functor.map_comp, hV, Functor.map_comp, ← Category.assoc, ← Category.assoc,
    ← f5sheaf_restrictNest_unit h]
  simp only [Category.assoc]

theorem f5sheaf_restrictNest_matHom {V W : X.Opens} (h : W ≤ V) {ι κ : Type} [Fintype κ]
    (Y : Matrix κ ι Γ(V, ⊤)) :
    (f5sheaf_restrictFreeIso W.ι ι).hom ≫ (f5sheaf_restrictNest h).hom.app (f5sheaf_free X ι) ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
          ((f5sheaf_restrictFreeIso V.ι ι).inv ≫ f5sheaf_matHom Y) =
      f5sheaf_matHom (f5sheaf_matPullback (X.homOfLE h) Y) ≫
        (f5sheaf_restrictFreeIso (X.homOfLE h) κ).hom := by
  rw [Functor.map_comp, ← Category.assoc ((f5sheaf_restrictNest h).hom.app _),
    ← Category.assoc, f5sheaf_restrictNest_free, f5sheaf_restrict_matHom]

end HodgeLean.Foundations.Algebraic
