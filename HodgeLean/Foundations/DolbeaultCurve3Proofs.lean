import HodgeLean.Foundations.DolbeaultCurve3Defs
import HodgeLean.Foundations.DolbeaultCurve2
import HodgeLean.Foundations.Port.AlgebraicTopology.Sheaf.FlasqueGlobalSections

/-! # Proof obligations for the Dolbeault stage 3: acyclicity of the soft Dolbeault sheaves -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicGeometry ComplexPoint Opposite
open scoped ContDiff Manifold
open HodgeLean.RealDefs HodgeLean.Adapters

universe u

namespace HodgeLean.Foundations

theorem spec_isSoft_of_isFlasque_aux {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    [F.IsFlasque] : IsSoft F := by
  intro K U _ hKU s
  obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective
    (F.obj.map (homOfLE le_top : U ⟶ ⊤).op)).mp
    (TopCat.Presheaf.IsFlasque.epi (homOfLE le_top : U ⟶ ⊤).op) s
  refine ⟨U, le_rfl, hKU, t, ?_⟩
  rw [ht]
  exact (TopCat.Presheaf.restrict_self (F := F.obj) s).symm

section dolb3a
variable {T : TopCat.{u}}

lemma dolb3a_res_res (F : TopCat.Sheaf AddCommGrpCat.{u} T) {U V W : Opens T} (h₁ : U ≤ V)
    (h₂ : V ≤ W) (x : F.obj.obj (op W)) :
    F.obj.map (homOfLE h₁).op (F.obj.map (homOfLE h₂).op x) =
      F.obj.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

lemma dolb3a_res_nat {F G : TopCat.Sheaf AddCommGrpCat.{u} T} (g : F ⟶ G) {U V : Opens T}
    (h : U ≤ V) (x : F.obj.obj (op V)) :
    g.hom.app (op U) (F.obj.map (homOfLE h).op x) =
      G.obj.map (homOfLE h).op (g.hom.app (op V) x) := by
  rw [← ConcreteCategory.comp_apply, NatTrans.naturality, ConcreteCategory.comp_apply]

set_option backward.isDefEq.respectTransparency false in
lemma dolb3a_fg {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (U : Opens T)
    (x : S.X₁.obj.obj (op U)) : S.g.hom.app (op U) (S.f.hom.app (op U) x) = 0 := by
  have : (S.f.hom.app (op U) ≫ S.g.hom.app (op U)) = 0 := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, S.zero]; rfl
  rw [← ConcreteCategory.comp_apply, this]; rfl

lemma dolb3a_glue₂ (F : TopCat.Sheaf AddCommGrpCat.{u} T) {V₁ V₂ : Opens T}
    (s₁ : F.obj.obj (op V₁)) (s₂ : F.obj.obj (op V₂))
    (h : F.obj.map (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op s₁ =
      F.obj.map (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op s₂) :
    ∃ s : F.obj.obj (op (V₁ ⊔ V₂)), F.obj.map (homOfLE (le_sup_left : V₁ ≤ V₁ ⊔ V₂)).op s = s₁ ∧
      F.obj.map (homOfLE (le_sup_right : V₂ ≤ V₁ ⊔ V₂)).op s = s₂ := by
  let f : Fin 2 → Opens T := ![V₁, V₂]
  let sf : (i : Fin 2) → F.obj.obj (op (f i))
    | 0 => s₁
    | 1 => s₂
  have h' : F.obj.map (homOfLE (inf_le_left : V₂ ⊓ V₁ ≤ V₂)).op s₂ =
      F.obj.map (homOfLE (inf_le_right : V₂ ⊓ V₁ ≤ V₁)).op s₁ := by
    have := congrArg (F.obj.map (homOfLE (le_of_eq (inf_comm _ _) : V₂ ⊓ V₁ ≤ V₁ ⊓ V₂)).op) h
    rw [dolb3a_res_res, dolb3a_res_res] at this
    exact this.symm
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' f (V₁ ⊔ V₂)
    (fun i => homOfLE (by fin_cases i <;> simp [f]))
    (sup_le (le_iSup f 0) (le_iSup f 1)) sf (by
      intro i j
      fin_cases i <;> fin_cases j
      · rfl
      · exact h
      · exact h'
      · rfl)
  exact ⟨s, hs 0, hs 1⟩

end dolb3a

theorem spec_liftsNear_union_aux {T : TopCat.{u}} [NormalSpace T]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    (hA : IsSoft S.X₁) {K₁ K₂ : Set T} (hK₁ : IsClosed K₁) (hK₂ : IsClosed K₂) {U : Opens T}
    (c : S.X₃.obj.obj (op U)) (h₁ : LiftsNear S.g K₁ c) (h₂ : LiftsNear S.g K₂ c) :
    LiftsNear S.g (K₁ ∪ K₂) c := by
  obtain ⟨V₁, hV₁, hK₁V, b₁, hb₁⟩ := h₁
  obtain ⟨V₂, hV₂, hK₂V, b₂, hb₂⟩ := h₂
  let d : S.X₂.obj.obj (op (V₁ ⊓ V₂)) :=
    S.X₂.obj.map (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op b₁ -
      S.X₂.obj.map (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op b₂
  have hd : S.g.hom.app (op (V₁ ⊓ V₂)) d = 0 := by
    simp only [d, map_sub, dolb3a_res_nat, hb₁, hb₂, dolb3a_res_res, sub_self]
  obtain ⟨a, ha⟩ := TopCat.Sheaf.sections_exact_of_left_exact hS.exact hS.mono_f d hd
  obtain ⟨W, hWI, hKW, a', ha'⟩ := hA (K₁ ∩ K₂) (V₁ ⊓ V₂) (hK₁.inter hK₂)
    (fun x hx => ⟨hK₁V hx.1, hK₂V hx.2⟩) a
  let b₂' : S.X₂.obj.obj (op V₂) :=
    b₂ + S.f.hom.app (op V₂) (S.X₁.obj.map (homOfLE (le_top : V₂ ≤ ⊤)).op a')
  have hb₂' : S.g.hom.app (op V₂) b₂' = S.X₃.obj.map (homOfLE hV₂).op c := by
    simp only [b₂', map_add, dolb3a_fg, add_zero, hb₂]
  have hWV₁ : W ≤ V₁ := hWI.trans inf_le_left
  have hWV₂ : W ≤ V₂ := hWI.trans inf_le_right
  have hagree : S.X₂.obj.map (homOfLE hWV₁).op b₁ = S.X₂.obj.map (homOfLE hWV₂).op b₂' := by
    have e1 := congrArg (S.X₂.obj.map (homOfLE hWI).op) ha
    rw [← dolb3a_res_nat] at e1
    simp only [d, map_sub, dolb3a_res_res] at e1
    simp only [b₂', map_add, ← dolb3a_res_nat, dolb3a_res_res]
    rw [eq_sub_iff_add_eq] at e1
    rw [← e1, add_comm, ← ha']
  have hsep : Disjoint (K₁ \ W) (K₂ \ W) := by
    rw [Set.disjoint_left]
    rintro x ⟨hx₁, hxW⟩ ⟨hx₂, -⟩
    exact hxW (hKW ⟨hx₁, hx₂⟩)
  obtain ⟨O₁, O₂, hO₁, hO₂, hKO₁, hKO₂, hO⟩ :=
    normal_separation (hK₁.sdiff W.isOpen) (hK₂.sdiff W.isOpen) hsep
  let V₁' : Opens T := V₁ ⊓ (⟨O₁, hO₁⟩ ⊔ W)
  let V₂' : Opens T := V₂ ⊓ (⟨O₂, hO₂⟩ ⊔ W)
  have hV₁' : V₁' ≤ V₁ := inf_le_left
  have hV₂' : V₂' ≤ V₂ := inf_le_left
  have hint : V₁' ⊓ V₂' ≤ W := by
    rintro x ⟨⟨-, hx₁⟩, ⟨-, hx₂⟩⟩
    by_contra hxW
    have h1 : x ∈ O₁ := by
      rcases hx₁ with h | h
      · exact h
      · exact absurd h hxW
    have h2 : x ∈ O₂ := by
      rcases hx₂ with h | h
      · exact h
      · exact absurd h hxW
    exact Set.disjoint_left.mp hO h1 h2
  have hK₁' : K₁ ⊆ V₁' := by
    intro x hx
    refine ⟨hK₁V hx, ?_⟩
    by_cases hxW : x ∈ W
    · exact Or.inr hxW
    · exact Or.inl (hKO₁ ⟨hx, hxW⟩)
  have hK₂' : K₂ ⊆ V₂' := by
    intro x hx
    refine ⟨hK₂V hx, ?_⟩
    by_cases hxW : x ∈ W
    · exact Or.inr hxW
    · exact Or.inl (hKO₂ ⟨hx, hxW⟩)
  obtain ⟨b, hb₁', hb₂''⟩ := dolb3a_glue₂ S.X₂ (S.X₂.obj.map (homOfLE hV₁').op b₁)
    (S.X₂.obj.map (homOfLE hV₂').op b₂') (by
      rw [dolb3a_res_res, dolb3a_res_res,
        ← dolb3a_res_res S.X₂ hint hWV₁, ← dolb3a_res_res S.X₂ hint hWV₂, hagree])
  have hVU : V₁' ⊔ V₂' ≤ U := sup_le (hV₁'.trans hV₁) (hV₂'.trans hV₂)
  refine ⟨V₁' ⊔ V₂', hVU, Set.union_subset_union hK₁' hK₂' |>.trans (fun x hx => ?_), b, ?_⟩
  · rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr h
  · refine S.X₃.eq_of_locally_eq₂ (homOfLE (le_sup_left : V₁' ≤ V₁' ⊔ V₂'))
      (homOfLE (le_sup_right : V₂' ≤ V₁' ⊔ V₂')) le_rfl _ _ ?_ ?_
    · rw [← dolb3a_res_nat, hb₁', dolb3a_res_nat, hb₁, dolb3a_res_res, dolb3a_res_res]
    · rw [← dolb3a_res_nat, hb₂'', dolb3a_res_nat, hb₂', dolb3a_res_res, dolb3a_res_res]

lemma dolb3a_liftsNear_empty {T : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} {U : Opens T}
    (c : S.X₃.obj.obj (op U)) : LiftsNear S.g ∅ c := by
  refine ⟨⊥, bot_le, Set.empty_subset _, 0, ?_⟩
  rw [map_zero]
  exact S.X₃.eq_of_locally_eq' (U := (PEmpty.elim : PEmpty.{u + 1} → Opens T)) ⊥
    (fun i => i.elim) bot_le _ _ (fun i => i.elim)

theorem spec_liftsNear_of_isClosed_aux {T : TopCat.{u}} [CompactSpace T] [T2Space T]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    (hA : IsSoft S.X₁) {K : Set T} (hK : IsClosed K) {U : Opens T} (hKU : K ⊆ U)
    (c : S.X₃.obj.obj (op U)) :
    LiftsNear S.g K c := by
  classical
  have hloc := (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr hS.epi_g)
  have key : ∀ x ∈ K, ∃ N : Set T, IsClosed N ∧ N ∈ nhds x ∧ LiftsNear S.g N c := by
    intro x hx
    obtain ⟨W, hWU, ⟨b, hb⟩, hxW⟩ := hloc U c x (hKU hx)
    obtain ⟨N, hN, hNc, hNW⟩ := exists_mem_nhds_isClosed_subset (W.isOpen.mem_nhds hxW)
    exact ⟨N, hNc, hN, W, hWU, hNW, b, hb⟩
  choose! N hNc hN hNl using key
  obtain ⟨t, htK, hcover⟩ := hK.isCompact.elim_nhds_subcover N hN
  have hfin : ∀ s : Finset T, (∀ x ∈ s, x ∈ K) → LiftsNear S.g (⋃ x ∈ s, N x) c := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using dolb3a_liftsNear_empty c
    | insert a s ha ih =>
      intro hs
      rw [Finset.set_biUnion_insert]
      have hs' : ∀ x ∈ s, x ∈ K := fun x hx => hs x (Finset.mem_insert_of_mem hx)
      exact spec_liftsNear_union_aux hS hA (hNc a (hs a (Finset.mem_insert_self a s)))
        (s.finite_toSet.isClosed_biUnion fun i hi => hNc i (hs' i hi)) c
        (hNl a (hs a (Finset.mem_insert_self a s))) (ih hs')
  obtain ⟨V, hVU, hKV, b, hb⟩ := hfin t htK
  exact ⟨V, hVU, hcover.trans hKV, b, hb⟩

theorem spec_surjective_globalSections_of_isSoft_aux {T : TopCat.{u}} [CompactSpace T]
    [T2Space T] {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    (hA : IsSoft S.X₁) :
    Function.Surjective (S.g.hom.app (op ⊤)) := by
  intro c
  obtain ⟨V, hV, hKV, b, hb⟩ := spec_liftsNear_of_isClosed_aux hS hA isClosed_univ
    (Set.subset_univ _ : Set.univ ⊆ ((⊤ : Opens T) : Set T)) c
  obtain rfl : V = ⊤ := eq_top_iff.mpr (fun x _ => hKV (Set.mem_univ x))
  exact ⟨b, hb.trans (TopCat.Presheaf.restrict_self (F := S.X₃.obj) c)⟩

theorem spec_isSoft_of_shortExact_aux {T : TopCat.{u}} [CompactSpace T] [T2Space T]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    (h₁ : IsSoft S.X₁) (h₂ : IsSoft S.X₂) :
    IsSoft S.X₃ := by
  intro K U hK hKU c
  obtain ⟨V', hV'U, hKV', b, hb⟩ := spec_liftsNear_of_isClosed_aux hS h₁ hK hKU c
  obtain ⟨V, hVV', hKV, t, ht⟩ := h₂ K V' hK hKV' b
  refine ⟨V, hVV'.trans hV'U, hKV, S.g.hom.app (op ⊤) t, ?_⟩
  rw [← dolb3a_res_nat, ht, dolb3a_res_nat, hb, dolb3a_res_res]

section dolb3a_ext
attribute [local instance] TopCat.Sheaf.extAddCommGroup

/-- Every positive-degree cohomology class of a soft sheaf on a compact Hausdorff space is zero:
the dimension shift of `TopCat.Sheaf.IsFlasque.cohomology_succ_eq_zero`, with softness in place of
flasqueness. -/
lemma dolb3a_cohomology_succ_eq_zero {T : TopCat.{u}} [CompactSpace T] [T2Space T]
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) (hF : IsSoft F) (n : ℕ)
    (x : Abelian.Ext 𝓒(T; ULift.{u} ℤ) F (n + 1)) : x = 0 := by
  induction n generalizing F with
  | zero =>
      let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T) :=
        ShortComplex.mk (Injective.ι F) (Limits.cokernel.π (Injective.ι F))
          (Limits.cokernel.condition (Injective.ι F))
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
      let : Injective S.X₂ := by dsimp [S]; infer_instance
      have hx : x.comp (Abelian.Ext.mk₀ S.f) (add_zero 1) = 0 := by
        apply Abelian.Ext.eq_zero_of_injective
      obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x hx rfl
      have hg : Function.Surjective (S.g.hom.app (op (⊤ : Opens T))) :=
        spec_surjective_globalSections_of_isSoft_aux hS hF
      obtain ⟨z, hz⟩ := hg (TopCat.Sheaf.IsFlasque.globalSectionsEquiv S.X₃ y)
      let z' : Abelian.Ext 𝓒(T; ULift.{u} ℤ) S.X₂ 0 :=
        (TopCat.Sheaf.IsFlasque.globalSectionsEquiv S.X₂).symm z
      have hz' : z'.comp (Abelian.Ext.mk₀ S.g) (add_zero 0) = y := by
        apply (TopCat.Sheaf.IsFlasque.globalSectionsEquiv S.X₃).injective
        calc
          TopCat.Sheaf.IsFlasque.globalSectionsEquiv S.X₃
              (z'.comp (Abelian.Ext.mk₀ S.g) (add_zero 0)) =
              S.g.hom.app (op (⊤ : Opens T))
                (TopCat.Sheaf.IsFlasque.globalSectionsEquiv S.X₂ z') :=
            (TopCat.Sheaf.IsFlasque.globalSectionsEquiv_naturality S.g z').symm
          _ = TopCat.Sheaf.IsFlasque.globalSectionsEquiv S.X₃ y := by
            simpa only [z', Equiv.apply_symm_apply] using hz
      rw [← hy, ← hz', Abelian.Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
        Abelian.Ext.comp_zero]
  | succ n ih =>
      let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T) :=
        ShortComplex.mk (Injective.ι F) (Limits.cokernel.π (Injective.ι F))
          (Limits.cokernel.condition (Injective.ι F))
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
      have := TopCat.Sheaf.injective_isFlasque T (Injective.under F)
      have h₃ : IsSoft S.X₃ :=
        spec_isSoft_of_shortExact_aux hS hF (spec_isSoft_of_isFlasque_aux (Injective.under F))
      let : Injective S.X₂ := by dsimp [S]; infer_instance
      have hx : x.comp (Abelian.Ext.mk₀ S.f) (add_zero (n + 2)) = 0 := by
        apply Abelian.Ext.eq_zero_of_injective
      obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x hx rfl
      have hy0 : y = 0 := ih S.X₃ h₃ y
      rw [← hy, hy0]
      exact Abelian.Ext.zero_comp _ _ _ _ _

end dolb3a_ext

theorem spec_subsingleton_cohomology_succ_of_isSoft_aux {T : TopCat.{u}} [CompactSpace T]
    [T2Space T] (F : TopCat.Sheaf AddCommGrpCat.{u} T) (hF : IsSoft F) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  constructor
  intro x y
  change Abelian.Ext 𝓒(T; ULift.{u} ℤ) F (n + 1) at x y
  rw [dolb3a_cohomology_succ_eq_zero F hF n x, dolb3a_cohomology_succ_eq_zero F hF n y]

theorem spec_nonempty_hypercohomology_single_equiv_aux (X : Over (Spec ↧ℂ))
    (F : AnalyticAdditiveSheaf X) (n : ℕ) :
    Nonempty (ℍ^(n : ℤ)(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj F) ≃ CategoryTheory.Sheaf.H F n) := by
  have h : HasExt.{0} (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat.{0}) := inferInstance
  have := h ((constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))) F
  exact ⟨(Localization.SmallShiftedHom.precompEquiv.{1} (W := analyticQuasiIsomorphisms X)
      (constantIntegerSheafComplexIntIsoSingleULift X).hom
      ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance) (a := (n : ℤ))).symm.trans
    (@Localization.SmallShiftedHom.chgUniv.{0, 1} _ _ _ _ _ _ _ _ _
      (analyticHasSmallLocalizedShiftedHom X _ _) this)⟩

theorem spec_subsingleton_hypercohomology_succ_of_isSoft_aux (X : Over (Spec ↧ℂ))
    [CompactSpace (ComplexPoint X)] [T2Space (ComplexPoint X)]
    (F : AnalyticAdditiveSheaf X) (hF : IsSoft F) (n : ℕ) :
    Subsingleton ℍ^((n + 1 : ℕ) : ℤ)(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj F) := by
  obtain ⟨e⟩ := spec_nonempty_hypercohomology_single_equiv_aux X F (n + 1)
  have := spec_subsingleton_cohomology_succ_of_isSoft_aux (T := TopCat.of (ComplexPoint X)) F hF n
  exact e.subsingleton

open Topology in
/-- A smooth cut-off: equal to `1` near the closed set `K` and to `0` near every point outside the
open set `U ⊇ K`. -/
lemma exists_smooth_cutoff_dolb3 {X : Over (Spec ↧ℂ)} {d : ℕ}
    [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]
    [SigmaCompactSpace (ComplexPoint X)] {K : Set (ComplexPoint X)}
    {U : Opens (TopCat.of (ComplexPoint X))} (hK : IsClosed K) (hKU : K ⊆ U) :
    ∃ ψ : ComplexPoint X → ℂ, ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) ∞ ψ ∧
      (∃ (V : Opens (TopCat.of (ComplexPoint X))) (_ : V ≤ U), K ⊆ V ∧ ∀ y ∈ V, ψ y = 1) ∧
      ∀ x ∉ U, ∀ᶠ y in 𝓝 x, ψ y = 0 := by
  have : LocallyCompactSpace (ComplexPoint X) :=
    Manifold.locallyCompact_of_finiteDimensional 𝓘(ℝ, Fin d → ℂ)
  have : ParacompactSpace (ComplexPoint X) := inferInstance
  have : NormalSpace (ComplexPoint X) := inferInstance
  obtain ⟨f, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, Fin d → ℂ)
    (n := ⊤) U.isOpen.isClosed_compl hK (Set.disjoint_compl_left_iff_subset.mpr hKU)
  obtain ⟨W, hWo, hKW, hW⟩ := mem_nhdsSet_iff_exists.mp h1
  refine ⟨fun y => (f y : ℂ), Complex.ofRealCLM.contMDiff.comp f.contMDiff,
    ⟨⟨W, hWo⟩ ⊓ U, inf_le_right, fun x hx => ⟨hKW hx, hKU hx⟩,
      fun y hy => by simp [show f y = 1 from hW hy.1]⟩, fun x hx => ?_⟩
  filter_upwards [h0.filter_mono (nhds_le_nhdsSet hx)] with y hy
  simp [hy]

theorem spec_isSoft_smoothFunctionSheaf_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]
    [SigmaCompactSpace (ComplexPoint X)] :
    IsSoft (smoothFunctionSheaf X d) := by
  intro K U hK hKU s₀
  let s : C^∞⟮𝓘(ℝ, Fin d → ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯ := s₀
  obtain ⟨ψ, hψ, ⟨V, hVU, hKV, hV⟩, h0⟩ := exists_smooth_cutoff_dolb3 (d := d) hK hKU
  have hg : ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, ℂ) ∞ (fun y => ψ y * extendSection s y) := by
    intro x
    by_cases hx : x ∈ U
    · exact (hψ x).mul (contMDiffAt_extendSection s ⟨x, hx⟩)
    · refine (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [h0 x hx] with y hy
      simp [hy]
  refine ⟨V, hVU, hKV, ⟨fun y => ψ y * extendSection s y, hg.comp contMDiff_subtype_val⟩, ?_⟩
  apply ContMDiffMap.ext
  intro y
  change ψ y * extendSection s y = s ⟨y, hVU y.2⟩
  rw [hV y y.2, one_mul, extendSection_of_mem]

theorem spec_isSoft_zeroOneFormSheaf_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]
    [SigmaCompactSpace (ComplexPoint X)] :
    IsSoft (zeroOneFormSheaf X d) := by
  intro K U hK hKU σ
  obtain ⟨ψ, hψ, ⟨V, hVU, hKV, hV⟩, h0⟩ := exists_smooth_cutoff_dolb3 (d := d) hK hKU
  let τ : ComplexPoint X → (Fin d → ℂ) →L[ℝ] ℂ := fun y => ψ y • extendSection σ.1 y
  have hτ : ∀ x, IsZeroOneFormAt X d τ x := by
    intro x
    by_cases hx : x ∈ U
    · exact spec_isZeroOneFormAt_smul (hψ x) (σ.2 ⟨x, hx⟩)
    · refine (show IsZeroOneFormAt X d (fun _ => 0) x from
        ⟨map_zero _, by simpa using contMDiffAt_const⟩).congr ?_
      filter_upwards [h0 x hx] with y hy
      simp only [τ, hy]
      exact (zero_smul ℂ (extendSection (σ.1 : U → (Fin d → ℂ) →L[ℝ] ℂ) y)).symm
  refine ⟨V, hVU, hKV, ⟨fun y => τ y, fun x => (hτ x).congr ?_⟩, ?_⟩
  · exact Filter.Eventually.of_forall fun y =>
      (extendSection_of_mem (U := ((⊤ : Opens (TopCat.of (ComplexPoint X))) : Set (ComplexPoint X)))
        (fun y : (⊤ : Opens (TopCat.of (ComplexPoint X))) => τ y) (Set.mem_univ y)).symm
  · apply Subtype.ext
    funext y
    change ψ y • extendSection σ.1 y = σ.1 ⟨y, hVU y.2⟩
    rw [hV y y.2, one_smul, extendSection_of_mem]

theorem spec_subsingleton_hypercohomology_succ_smoothFunctionSheaf_aux (X : Over (Spec ↧ℂ))
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] [IsProjective X.hom] (n : ℕ) :
    Subsingleton ℍ^((n + 1 : ℕ) : ℤ)(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X d)) :=
  spec_subsingleton_hypercohomology_succ_of_isSoft_aux X _
    (spec_isSoft_smoothFunctionSheaf_aux X d) n

theorem spec_subsingleton_hypercohomology_succ_zeroOneFormSheaf_aux (X : Over (Spec ↧ℂ))
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] [IsProjective X.hom] (n : ℕ) :
    Subsingleton ℍ^((n + 1 : ℕ) : ℤ)(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X d)) :=
  spec_subsingleton_hypercohomology_succ_of_isSoft_aux X _
    (spec_isSoft_zeroOneFormSheaf_aux X d) n

theorem spec_subsingleton_hypercohomology_two_of_curve_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProjective X.hom] :
    Subsingleton ℍ^2(X; holomorphicFormsShifted X 0) :=
  spec_subsingleton_hypercohomology_two_of_acyclic X (SmoothOfRelativeDimension.dim_eq X.hom 1)
    (spec_subsingleton_hypercohomology_succ_smoothFunctionSheaf_aux X (dim X.left) 1)
    (spec_subsingleton_hypercohomology_succ_zeroOneFormSheaf_aux X (dim X.left) 0)

theorem spec_cycleClassIsHodge_of_curve_of_projective_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProjective X.hom] :
    CycleClassIsHodge X :=
  spec_cycleClassIsHodge_of_curve_of_acyclic X
    (spec_subsingleton_hypercohomology_succ_smoothFunctionSheaf_aux X (dim X.left) 1)
    (spec_subsingleton_hypercohomology_succ_zeroOneFormSheaf_aux X (dim X.left) 0)

end HodgeLean.Foundations
