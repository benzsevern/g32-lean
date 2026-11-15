module

public import HodgeLean.Foundations.Program.SchoenExceptionalSoft
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.LocallySurjective

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry
universe u
namespace HodgeLean.Foundations.Program

attribute [local instance] TopCat.Sheaf.extAddCommGroup

def s3_globalSectionsEquiv {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    Abelian.Ext 𝓒(T; ULift.{u} ℤ) F 0 ≃ F.obj.obj (op (⊤ : Opens T)) :=
  letI : AddCommGroup (CategoryTheory.Sheaf.H F 0) := TopCat.Sheaf.extAddCommGroup
  (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop).toEquiv

set_option backward.isDefEq.respectTransparency false in
lemma s3_globalSectionsEquiv_naturality {T : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} T} (f : F ⟶ G)
    (x : Abelian.Ext 𝓒(T; ULift.{u} ℤ) F 0) :
    f.hom.app (op (⊤ : Opens T)) (s3_globalSectionsEquiv F x) =
      s3_globalSectionsEquiv G (x.comp (Abelian.Ext.mk₀ f) (add_zero 0)) :=
  CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop f x

theorem s3_isSoft_of_isFlasque {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    [F.IsFlasque] : (∀ (K : Set T) (U : Opens T), IsClosed K → K ⊆ U → ∀ s : F.obj.obj (op U),
      ∃ (V : Opens T) (hV : V ≤ U), K ⊆ V ∧ ∃ t : F.obj.obj (op ⊤),
        F.obj.map (homOfLE le_top : V ⟶ ⊤).op t = F.obj.map (homOfLE hV).op s) := by
  intro K U _ hKU s
  obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective
    (F.obj.map (homOfLE le_top : U ⟶ ⊤).op)).mp
    (TopCat.Presheaf.IsFlasque.epi (homOfLE le_top : U ⟶ ⊤).op) s
  refine ⟨U, le_rfl, hKU, t, ?_⟩
  rw [ht]
  exact (TopCat.Presheaf.restrict_self (F := F.obj) s).symm

section dolb3a
variable {T : TopCat.{u}}

lemma s3_soft_res_res (F : TopCat.Sheaf AddCommGrpCat.{u} T) {U V W : Opens T} (h₁ : U ≤ V)
    (h₂ : V ≤ W) (x : F.obj.obj (op W)) :
    F.obj.map (homOfLE h₁).op (F.obj.map (homOfLE h₂).op x) =
      F.obj.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

lemma s3_soft_res_nat {F G : TopCat.Sheaf AddCommGrpCat.{u} T} (g : F ⟶ G) {U V : Opens T}
    (h : U ≤ V) (x : F.obj.obj (op V)) :
    g.hom.app (op U) (F.obj.map (homOfLE h).op x) =
      G.obj.map (homOfLE h).op (g.hom.app (op V) x) := by
  rw [← ConcreteCategory.comp_apply, NatTrans.naturality, ConcreteCategory.comp_apply]

set_option backward.isDefEq.respectTransparency false in
lemma s3_soft_fg {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (U : Opens T)
    (x : S.X₁.obj.obj (op U)) : S.g.hom.app (op U) (S.f.hom.app (op U) x) = 0 := by
  have : (S.f.hom.app (op U) ≫ S.g.hom.app (op U)) = 0 := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, S.zero]; rfl
  rw [← ConcreteCategory.comp_apply, this]; rfl

lemma s3_soft_glue₂ (F : TopCat.Sheaf AddCommGrpCat.{u} T) {V₁ V₂ : Opens T}
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
    rw [s3_soft_res_res, s3_soft_res_res] at this
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

theorem s3_liftsNear_union {T : TopCat.{u}} [NormalSpace T]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    (hA : (∀ (K : Set T) (U : Opens T), IsClosed K → K ⊆ U → ∀ s : S.X₁.obj.obj (op U),
      ∃ (V : Opens T) (hV : V ≤ U), K ⊆ V ∧ ∃ t : S.X₁.obj.obj (op ⊤),
        S.X₁.obj.map (homOfLE le_top : V ⟶ ⊤).op t = S.X₁.obj.map (homOfLE hV).op s)) {K₁ K₂ : Set T} (hK₁ : IsClosed K₁) (hK₂ : IsClosed K₂) {U : Opens T}
    (c : S.X₃.obj.obj (op U)) (h₁ : (∃ (V : Opens T) (hV : V ≤ U), K₁ ⊆ V ∧ ∃ b : S.X₂.obj.obj (op V),
      S.g.hom.app (op V) b = S.X₃.obj.map (homOfLE hV).op c)) (h₂ : (∃ (V : Opens T) (hV : V ≤ U), K₂ ⊆ V ∧ ∃ b : S.X₂.obj.obj (op V),
      S.g.hom.app (op V) b = S.X₃.obj.map (homOfLE hV).op c)) :
    (∃ (V : Opens T) (hV : V ≤ U), (K₁ ∪ K₂) ⊆ V ∧ ∃ b : S.X₂.obj.obj (op V),
      S.g.hom.app (op V) b = S.X₃.obj.map (homOfLE hV).op c) := by
  obtain ⟨V₁, hV₁, hK₁V, b₁, hb₁⟩ := h₁
  obtain ⟨V₂, hV₂, hK₂V, b₂, hb₂⟩ := h₂
  let d : S.X₂.obj.obj (op (V₁ ⊓ V₂)) :=
    S.X₂.obj.map (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op b₁ -
      S.X₂.obj.map (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op b₂
  have hd : S.g.hom.app (op (V₁ ⊓ V₂)) d = 0 := by
    simp only [d, map_sub, s3_soft_res_nat, hb₁, hb₂, s3_soft_res_res, sub_self]
  obtain ⟨a, ha⟩ := TopCat.Sheaf.sections_exact_of_left_exact hS.exact hS.mono_f d hd
  obtain ⟨W, hWI, hKW, a', ha'⟩ := hA (K₁ ∩ K₂) (V₁ ⊓ V₂) (hK₁.inter hK₂)
    (fun x hx => ⟨hK₁V hx.1, hK₂V hx.2⟩) a
  let b₂' : S.X₂.obj.obj (op V₂) :=
    b₂ + S.f.hom.app (op V₂) (S.X₁.obj.map (homOfLE (le_top : V₂ ≤ ⊤)).op a')
  have hb₂' : S.g.hom.app (op V₂) b₂' = S.X₃.obj.map (homOfLE hV₂).op c := by
    simp only [b₂', map_add, s3_soft_fg, add_zero, hb₂]
  have hWV₁ : W ≤ V₁ := hWI.trans inf_le_left
  have hWV₂ : W ≤ V₂ := hWI.trans inf_le_right
  have hagree : S.X₂.obj.map (homOfLE hWV₁).op b₁ = S.X₂.obj.map (homOfLE hWV₂).op b₂' := by
    have e1 := congrArg (S.X₂.obj.map (homOfLE hWI).op) ha
    rw [← s3_soft_res_nat] at e1
    simp only [d, map_sub, s3_soft_res_res] at e1
    simp only [b₂', map_add, ← s3_soft_res_nat, s3_soft_res_res]
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
  obtain ⟨b, hb₁', hb₂''⟩ := s3_soft_glue₂ S.X₂ (S.X₂.obj.map (homOfLE hV₁').op b₁)
    (S.X₂.obj.map (homOfLE hV₂').op b₂') (by
      rw [s3_soft_res_res, s3_soft_res_res,
        ← s3_soft_res_res S.X₂ hint hWV₁, ← s3_soft_res_res S.X₂ hint hWV₂, hagree])
  have hVU : V₁' ⊔ V₂' ≤ U := sup_le (hV₁'.trans hV₁) (hV₂'.trans hV₂)
  refine ⟨V₁' ⊔ V₂', hVU, Set.union_subset_union hK₁' hK₂' |>.trans (fun x hx => ?_), b, ?_⟩
  · rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr h
  · refine S.X₃.eq_of_locally_eq₂ (homOfLE (le_sup_left : V₁' ≤ V₁' ⊔ V₂'))
      (homOfLE (le_sup_right : V₂' ≤ V₁' ⊔ V₂')) le_rfl _ _ ?_ ?_
    · rw [← s3_soft_res_nat, hb₁', s3_soft_res_nat, hb₁, s3_soft_res_res, s3_soft_res_res]
    · rw [← s3_soft_res_nat, hb₂'', s3_soft_res_nat, hb₂', s3_soft_res_res, s3_soft_res_res]

lemma s3_soft_liftsNear_empty {T : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} {U : Opens T}
    (c : S.X₃.obj.obj (op U)) : (∃ (V : Opens T) (hV : V ≤ U), (∅ : Set T) ⊆ V ∧ ∃ b : S.X₂.obj.obj (op V),
      S.g.hom.app (op V) b = S.X₃.obj.map (homOfLE hV).op c) := by
  refine ⟨⊥, bot_le, Set.empty_subset _, 0, ?_⟩
  rw [map_zero]
  exact S.X₃.eq_of_locally_eq' (U := (PEmpty.elim : PEmpty.{u + 1} → Opens T)) ⊥
    (fun i => i.elim) bot_le _ _ (fun i => i.elim)

theorem s3_liftsNear_of_isClosed {T : TopCat.{u}} [CompactSpace T] [T2Space T]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    (hA : (∀ (K : Set T) (U : Opens T), IsClosed K → K ⊆ U → ∀ s : S.X₁.obj.obj (op U),
      ∃ (V : Opens T) (hV : V ≤ U), K ⊆ V ∧ ∃ t : S.X₁.obj.obj (op ⊤),
        S.X₁.obj.map (homOfLE le_top : V ⟶ ⊤).op t = S.X₁.obj.map (homOfLE hV).op s)) {K : Set T} (hK : IsClosed K) {U : Opens T} (hKU : K ⊆ U)
    (c : S.X₃.obj.obj (op U)) :
    (∃ (V : Opens T) (hV : V ≤ U), K ⊆ V ∧ ∃ b : S.X₂.obj.obj (op V),
      S.g.hom.app (op V) b = S.X₃.obj.map (homOfLE hV).op c) := by
  classical
  have hloc := (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr hS.epi_g)
  have key : ∀ x ∈ K, ∃ N : Set T, IsClosed N ∧ N ∈ nhds x ∧ (∃ (V : Opens T) (hV : V ≤ U), N ⊆ V ∧ ∃ b : S.X₂.obj.obj (op V),
      S.g.hom.app (op V) b = S.X₃.obj.map (homOfLE hV).op c) := by
    intro x hx
    obtain ⟨W, hWU, ⟨b, hb⟩, hxW⟩ := hloc U c x (hKU hx)
    obtain ⟨N, hN, hNc, hNW⟩ := exists_mem_nhds_isClosed_subset (W.isOpen.mem_nhds hxW)
    exact ⟨N, hNc, hN, W, hWU, hNW, b, hb⟩
  choose! N hNc hN hNl using key
  obtain ⟨t, htK, hcover⟩ := hK.isCompact.elim_nhds_subcover N hN
  have hfin : ∀ s : Finset T, (∀ x ∈ s, x ∈ K) → (∃ (V : Opens T) (hV : V ≤ U), (⋃ x ∈ s, N x) ⊆ V ∧ ∃ b : S.X₂.obj.obj (op V),
      S.g.hom.app (op V) b = S.X₃.obj.map (homOfLE hV).op c) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using s3_soft_liftsNear_empty c
    | insert a s ha ih =>
      intro hs
      rw [Finset.set_biUnion_insert]
      have hs' : ∀ x ∈ s, x ∈ K := fun x hx => hs x (Finset.mem_insert_of_mem hx)
      exact s3_liftsNear_union hS hA (hNc a (hs a (Finset.mem_insert_self a s)))
        (s.finite_toSet.isClosed_biUnion fun i hi => hNc i (hs' i hi)) c
        (hNl a (hs a (Finset.mem_insert_self a s))) (ih hs')
  obtain ⟨V, hVU, hKV, b, hb⟩ := hfin t htK
  exact ⟨V, hVU, hcover.trans hKV, b, hb⟩

theorem s3_surjective_globalSections_of_isSoft {T : TopCat.{u}} [CompactSpace T]
    [T2Space T] {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    (hA : (∀ (K : Set T) (U : Opens T), IsClosed K → K ⊆ U → ∀ s : S.X₁.obj.obj (op U),
      ∃ (V : Opens T) (hV : V ≤ U), K ⊆ V ∧ ∃ t : S.X₁.obj.obj (op ⊤),
        S.X₁.obj.map (homOfLE le_top : V ⟶ ⊤).op t = S.X₁.obj.map (homOfLE hV).op s)) :
    Function.Surjective (S.g.hom.app (op ⊤)) := by
  intro c
  obtain ⟨V, hV, hKV, b, hb⟩ := s3_liftsNear_of_isClosed hS hA isClosed_univ
    (Set.subset_univ _ : Set.univ ⊆ ((⊤ : Opens T) : Set T)) c
  obtain rfl : V = ⊤ := eq_top_iff.mpr (fun x _ => hKV (Set.mem_univ x))
  exact ⟨b, hb.trans (TopCat.Presheaf.restrict_self (F := S.X₃.obj) c)⟩

theorem s3_isSoft_of_shortExact {T : TopCat.{u}} [CompactSpace T] [T2Space T]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    (h₁ : (∀ (K : Set T) (U : Opens T), IsClosed K → K ⊆ U → ∀ s : S.X₁.obj.obj (op U),
      ∃ (V : Opens T) (hV : V ≤ U), K ⊆ V ∧ ∃ t : S.X₁.obj.obj (op ⊤),
        S.X₁.obj.map (homOfLE le_top : V ⟶ ⊤).op t = S.X₁.obj.map (homOfLE hV).op s)) (h₂ : (∀ (K : Set T) (U : Opens T), IsClosed K → K ⊆ U → ∀ s : S.X₂.obj.obj (op U),
      ∃ (V : Opens T) (hV : V ≤ U), K ⊆ V ∧ ∃ t : S.X₂.obj.obj (op ⊤),
        S.X₂.obj.map (homOfLE le_top : V ⟶ ⊤).op t = S.X₂.obj.map (homOfLE hV).op s)) :
    (∀ (K : Set T) (U : Opens T), IsClosed K → K ⊆ U → ∀ s : S.X₃.obj.obj (op U),
      ∃ (V : Opens T) (hV : V ≤ U), K ⊆ V ∧ ∃ t : S.X₃.obj.obj (op ⊤),
        S.X₃.obj.map (homOfLE le_top : V ⟶ ⊤).op t = S.X₃.obj.map (homOfLE hV).op s) := by
  intro K U hK hKU c
  obtain ⟨V', hV'U, hKV', b, hb⟩ := s3_liftsNear_of_isClosed hS h₁ hK hKU c
  obtain ⟨V, hVV', hKV, t, ht⟩ := h₂ K V' hK hKV' b
  refine ⟨V, hVV'.trans hV'U, hKV, S.g.hom.app (op ⊤) t, ?_⟩
  rw [← s3_soft_res_nat, ht, s3_soft_res_nat, hb, s3_soft_res_res]

section s3_soft_ext
attribute [local instance] TopCat.Sheaf.extAddCommGroup


lemma s3_soft_cohomology_succ_eq_zero {T : TopCat.{u}} [CompactSpace T] [T2Space T]
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) (hF : (∀ (K : Set T) (U : Opens T), IsClosed K → K ⊆ U → ∀ s : F.obj.obj (op U),
      ∃ (V : Opens T) (hV : V ≤ U), K ⊆ V ∧ ∃ t : F.obj.obj (op ⊤),
        F.obj.map (homOfLE le_top : V ⟶ ⊤).op t = F.obj.map (homOfLE hV).op s)) (n : ℕ)
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
        s3_surjective_globalSections_of_isSoft hS hF
      obtain ⟨z, hz⟩ := hg (s3_globalSectionsEquiv S.X₃ y)
      let z' : Abelian.Ext 𝓒(T; ULift.{u} ℤ) S.X₂ 0 :=
        (s3_globalSectionsEquiv S.X₂).symm z
      have hz' : z'.comp (Abelian.Ext.mk₀ S.g) (add_zero 0) = y := by
        apply (s3_globalSectionsEquiv S.X₃).injective
        calc
          s3_globalSectionsEquiv S.X₃
              (z'.comp (Abelian.Ext.mk₀ S.g) (add_zero 0)) =
              S.g.hom.app (op (⊤ : Opens T))
                (s3_globalSectionsEquiv S.X₂ z') :=
            (s3_globalSectionsEquiv_naturality S.g z').symm
          _ = s3_globalSectionsEquiv S.X₃ y := by
            simpa only [z', Equiv.apply_symm_apply] using hz
      rw [← hy, ← hz', Abelian.Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
        Abelian.Ext.comp_zero]
  | succ n ih =>
      let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T) :=
        ShortComplex.mk (Injective.ι F) (Limits.cokernel.π (Injective.ι F))
          (Limits.cokernel.condition (Injective.ι F))
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
      have := TopCat.Sheaf.injective_isFlasque T (Injective.under F)
      have h₃ : (∀ (K : Set T) (U : Opens T), IsClosed K → K ⊆ U → ∀ s : S.X₃.obj.obj (op U),
      ∃ (V : Opens T) (hV : V ≤ U), K ⊆ V ∧ ∃ t : S.X₃.obj.obj (op ⊤),
        S.X₃.obj.map (homOfLE le_top : V ⟶ ⊤).op t = S.X₃.obj.map (homOfLE hV).op s) :=
        s3_isSoft_of_shortExact hS hF (s3_isSoft_of_isFlasque (Injective.under F))
      let : Injective S.X₂ := by dsimp [S]; infer_instance
      have hx : x.comp (Abelian.Ext.mk₀ S.f) (add_zero (n + 2)) = 0 := by
        apply Abelian.Ext.eq_zero_of_injective
      obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x hx rfl
      have hy0 : y = 0 := ih S.X₃ h₃ y
      rw [← hy, hy0]
      exact Abelian.Ext.zero_comp _ _ _ _ _

end s3_soft_ext

theorem s3_subsingleton_cohomology_succ_of_isSoft {T : TopCat.{u}} [CompactSpace T]
    [T2Space T] (F : TopCat.Sheaf AddCommGrpCat.{u} T) (hF : (∀ (K : Set T) (U : Opens T), IsClosed K → K ⊆ U → ∀ s : F.obj.obj (op U),
      ∃ (V : Opens T) (hV : V ≤ U), K ⊆ V ∧ ∃ t : F.obj.obj (op ⊤),
        F.obj.map (homOfLE le_top : V ⟶ ⊤).op t = F.obj.map (homOfLE hV).op s)) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  constructor
  intro x y
  change Abelian.Ext 𝓒(T; ULift.{u} ℤ) F (n + 1) at x y
  rw [s3_soft_cohomology_succ_eq_zero F hF n x, s3_soft_cohomology_succ_eq_zero F hF n y]


end HodgeLean.Foundations.Program
