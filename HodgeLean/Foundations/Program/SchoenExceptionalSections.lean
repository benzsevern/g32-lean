module

public import HodgeLean.Foundations.Program.SchoenExceptionalProper
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheafify

@[expose] public noncomputable section
open scoped AlgebraicGeometry
open CategoryTheory Topology TopologicalSpace Opposite TopCat.Presheaf
namespace HodgeLean.Foundations.Program

theorem s3_sections_eq_near (X : TopCat) (F : TopCat.Sheaf AddCommGrpCat X)
    (K : Set X) (U V : Opens X) (hKU : K ⊆ U) (hKV : K ⊆ V)
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (h : ∀ x (hx : x ∈ K), F.presheaf.germ U x (hKU hx) s = F.presheaf.germ V x (hKV hx) t) :
    ∃ (W : Opens X) (hWU : W ≤ U) (hWV : W ≤ V), K ⊆ W ∧
      F.obj.map (homOfLE hWU).op s = F.obj.map (homOfLE hWV).op t := by
  classical
  choose W hxW iU iV he using fun x : K =>
    F.presheaf.germ_eq x.1 (hKU x.2) (hKV x.2) s t (h x.1 x.2)
  let O : Opens X := ⨆ x : K, W x
  have hOU : O ≤ U := iSup_le (fun x => (iU x).le)
  have hOV : O ≤ V := iSup_le (fun x => (iV x).le)
  refine ⟨O, hOU, hOV, ?_, ?_⟩
  · intro x hx
    exact (le_iSup W ⟨x, hx⟩) (hxW ⟨x, hx⟩)
  · apply F.eq_of_locally_eq' W O (fun x => homOfLE (le_iSup W x)) le_rfl
    intro x
    change F.presheaf.map _ (F.presheaf.map _ s) = F.presheaf.map _ (F.presheaf.map _ t)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    convert he x using 1

theorem s3_glue_compact_germs (X : TopCat) [T2Space X]
    (F : TopCat.Sheaf AddCommGrpCat X) (K L : Set X) (hK : IsCompact K) (hL : IsCompact L)
    (g : ∀ x : X, F.presheaf.stalk x) (U V : Opens X)
    (hKU : K ⊆ U) (hLV : L ⊆ V) (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (hs : ∀ x (hx : x ∈ K), F.presheaf.germ U x (hKU hx) s = g x)
    (ht : ∀ x (hx : x ∈ L), F.presheaf.germ V x (hLV hx) t = g x) :
    ∃ (O : Opens X) (hKO : K ∪ L ⊆ O) (r : F.obj.obj (op O)),
      ∀ x (hx : x ∈ K ∪ L), F.presheaf.germ O x (hKO hx) r = g x := by
  obtain ⟨W, hWU, hWV, hKW, he⟩ := s3_sections_eq_near X F (K ∩ L) U V
    (fun _ hx => hKU hx.1) (fun _ hx => hLV hx.2) s t
    (fun x hx => (hs x hx.1).trans (ht x hx.2).symm)
  have hd : Disjoint (K \ W) (L \ W) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxK, hxW⟩ ⟨hxL, _⟩
    exact hxW (hKW ⟨hxK, hxL⟩)
  obtain ⟨A, B, hA, hB, hKA, hLB, hAB⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hK.diff W.isOpen) (hL.diff W.isOpen) hd
  let U' : Opens X := U ⊓ (⟨A, hA⟩ ⊔ W)
  let V' : Opens X := V ⊓ (⟨B, hB⟩ ⊔ W)
  have hU'U : U' ≤ U := inf_le_left
  have hV'V : V' ≤ V := inf_le_left
  have hKU' : K ⊆ U' := by
    intro x hx
    refine ⟨hKU hx, ?_⟩
    by_cases hw : x ∈ W
    · exact Or.inr hw
    · exact Or.inl (hKA ⟨hx, hw⟩)
  have hLV' : L ⊆ V' := by
    intro x hx
    refine ⟨hLV hx, ?_⟩
    by_cases hw : x ∈ W
    · exact Or.inr hw
    · exact Or.inl (hLB ⟨hx, hw⟩)
  have hIW : U' ⊓ V' ≤ W := by
    rintro x ⟨⟨_, hxA⟩, ⟨_, hxB⟩⟩
    by_contra hw
    exact Set.disjoint_left.mp hAB (hxA.resolve_right hw) (hxB.resolve_right hw)
  let s' := F.obj.map (homOfLE hU'U).op s
  let t' := F.obj.map (homOfLE hV'V).op t
  have hst : F.obj.map (homOfLE (inf_le_left : U' ⊓ V' ≤ U')).op s' =
      F.obj.map (homOfLE (inf_le_right : U' ⊓ V' ≤ V')).op t' := by
    have e := congrArg (F.obj.map (homOfLE hIW).op) he
    dsimp only [s', t']
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at e ⊢
    convert e using 1
  let f : Fin 2 → Opens X := ![U', V']
  let sf : (j : Fin 2) → F.obj.obj (op (f j))
    | 0 => s'
    | 1 => t'
  have hst' : F.obj.map (homOfLE (inf_le_left : V' ⊓ U' ≤ V')).op t' =
      F.obj.map (homOfLE (inf_le_right : V' ⊓ U' ≤ U')).op s' := by
    have e := congrArg (F.obj.map (homOfLE (le_of_eq (inf_comm V' U'))).op) hst
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at e
    convert e.symm using 1
  obtain ⟨r, hr, _⟩ := F.existsUnique_gluing' f (U' ⊔ V')
    (fun j => homOfLE (by fin_cases j <;> simp [f]))
    (sup_le (le_iSup f 0) (le_iSup f 1)) sf (by
      intro j k
      fin_cases j <;> fin_cases k
      · rfl
      · exact hst
      · exact hst'
      · rfl)
  have hO : K ∪ L ⊆ (U' ⊔ V' : Opens X) := by
    rintro x (hx | hx)
    · exact Or.inl (hKU' hx)
    · exact Or.inr (hLV' hx)
  refine ⟨U' ⊔ V', hO, r, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · calc
      _ = F.presheaf.germ U' x (hKU' hx)
          (F.presheaf.map (homOfLE (le_sup_left : U' ≤ U' ⊔ V')).op r) :=
        (germ_res_apply F.presheaf _ x (hKU' hx) r).symm
      _ = F.presheaf.germ U' x (hKU' hx) s' := congrArg _ (hr 0)
      _ = F.presheaf.germ U x (hKU hx) s := germ_res_apply F.presheaf _ x _ s
      _ = g x := hs x hx
  · calc
      _ = F.presheaf.germ V' x (hLV' hx)
          (F.presheaf.map (homOfLE (le_sup_right : V' ≤ U' ⊔ V')).op r) :=
        (germ_res_apply F.presheaf _ x (hLV' hx) r).symm
      _ = F.presheaf.germ V' x (hLV' hx) t' := congrArg _ (hr 1)
      _ = F.presheaf.germ V x (hLV hx) t := germ_res_apply F.presheaf _ x _ t
      _ = g x := ht x hx

theorem s3_compact_germs_extend (X : TopCat) [T2Space X] [LocallyCompactSpace X]
    (F : TopCat.Sheaf AddCommGrpCat X) (K : Set X) (hK : IsCompact K)
    (g : ∀ x : X, F.presheaf.stalk x)
    (hg : ∀ x ∈ K, ∃ (U : Opens X), x ∈ U ∧ ∃ s : F.obj.obj (op U),
      ∀ y ∈ K, ∀ hy : y ∈ U, F.presheaf.germ U y hy s = g y) :
    ∃ (U : Opens X) (hKU : K ⊆ U) (s : F.obj.obj (op U)),
      ∀ x (hx : x ∈ K), F.presheaf.germ U x (hKU hx) s = g x := by
  classical
  obtain ⟨J, hJ, hKJ, hJK, U, hJU, s, hs⟩ :
      ∃ J : Set X, IsCompact J ∧ K ⊆ J ∧ J ⊆ K ∧
        ∃ (U : Opens X) (hJU : J ⊆ U) (s : F.obj.obj (op U)),
          ∀ x (hx : x ∈ J), F.presheaf.germ U x (hJU hx) s = g x := by
    apply hK.induction_on (p := fun A =>
      ∃ J : Set X, IsCompact J ∧ A ⊆ J ∧ J ⊆ K ∧
        ∃ (U : Opens X) (hJU : J ⊆ U) (s : F.obj.obj (op U)),
          ∀ x (hx : x ∈ J), F.presheaf.germ U x (hJU hx) s = g x)
    · exact ⟨∅, isCompact_empty, Set.empty_subset _, Set.empty_subset _,
        ⊥, Set.empty_subset _, 0, fun x hx => hx.elim⟩
    · rintro A B hAB ⟨J, hJ, hBJ, hJK, U, hJU, s, hs⟩
      exact ⟨J, hJ, hAB.trans hBJ, hJK, U, hJU, s, hs⟩
    · rintro A B ⟨J, hJ, hAJ, hJK, U, hJU, s, hs⟩
        ⟨L, hL, hBL, hLK, V, hLV, t, ht⟩
      obtain ⟨O, hO, r, hr⟩ := s3_glue_compact_germs X F J L hJ hL g U V hJU hLV s t hs ht
      exact ⟨J ∪ L, hJ.union hL, Set.union_subset_union hAJ hBL,
        Set.union_subset hJK hLK, O, hO, r, hr⟩
    · intro x hx
      obtain ⟨U, hxU, s, hs⟩ := hg x hx
      obtain ⟨C, hC, hxC, hCU⟩ := exists_compact_subset U.isOpen hxU
      refine ⟨K ∩ C, ?_, K ∩ C, hK.inter_right hC.isClosed, Set.Subset.rfl,
        Set.inter_subset_left, U, ?_, s, ?_⟩
      · exact Filter.inter_mem self_mem_nhdsWithin
          (nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.mp hxC))
      · exact fun y hy => hCU hy.2
      · intro y hy
        exact hs y hy.1 (hCU hy.2)
  exact ⟨U, hKJ.trans hJU, s, fun x hx => hs x (hKJ hx)⟩


theorem s3_fibre_germs_extend {X Y : TopCat} [T2Space X] [LocallyCompactSpace X]
    (p : X ⟶ Y) (hp : IsProperMap p) (F : TopCat.Sheaf AddCommGrpCat X)
    (y : Y) (g : ∀ x : X, F.presheaf.stalk x)
    (hg : ∀ x, p x = y → ∃ (U : Opens X), x ∈ U ∧ ∃ s : F.obj.obj (op U),
      ∀ z, p z = y → ∀ hz : z ∈ U, F.presheaf.germ U z hz s = g z) :
    ∃ (V : Opens Y) (hyV : y ∈ V) (s : F.obj.obj (op ((Opens.map p).obj V))),
      ∀ x (hx : p x = y),
        F.presheaf.germ ((Opens.map p).obj V) x (show p x ∈ V from hx.symm ▸ hyV) s = g x := by
  obtain ⟨U, hKU, s, hs⟩ := s3_compact_germs_extend X F {x | p x = y}
    (s3_fibre_compact p hp y) g hg
  obtain ⟨V, hV, hyV, hVU⟩ := s3_fibre_neighborhood p hp y U U.isOpen hKU
  let W : Opens Y := ⟨V, hV⟩
  have hWU : (Opens.map p).obj W ≤ U := hVU
  refine ⟨W, hyV, F.obj.map (homOfLE hWU).op s, ?_⟩
  intro x hx
  exact (germ_res_apply F.presheaf _ x (show p x ∈ V from hx.symm ▸ hyV) s).trans (hs x hx)

theorem s3_fibre_sections_eq_near {X Y : TopCat}
    (p : X ⟶ Y) (hp : IsProperMap p) (F : TopCat.Sheaf AddCommGrpCat X)
    (y : Y) (U V : Opens Y) (hyU : y ∈ U) (hyV : y ∈ V)
    (s : F.obj.obj (op ((Opens.map p).obj U)))
    (t : F.obj.obj (op ((Opens.map p).obj V)))
    (h : ∀ x (hx : p x = y),
      F.presheaf.germ ((Opens.map p).obj U) x (show p x ∈ U from hx.symm ▸ hyU) s =
        F.presheaf.germ ((Opens.map p).obj V) x (show p x ∈ V from hx.symm ▸ hyV) t) :
    ∃ (W : Opens Y) (hyW : y ∈ W) (hWU : W ≤ U) (hWV : W ≤ V),
      F.obj.map ((Opens.map p).map (homOfLE hWU)).op s =
        F.obj.map ((Opens.map p).map (homOfLE hWV)).op t := by
  obtain ⟨O, hOU, hOV, hKO, he⟩ := s3_sections_eq_near X F {x | p x = y}
    ((Opens.map p).obj U) ((Opens.map p).obj V)
    (fun x hx => show p x ∈ U from (show p x = y from hx).symm ▸ hyU) (fun x hx => show p x ∈ V from (show p x = y from hx).symm ▸ hyV) s t h
  obtain ⟨N, hN, hyN, hNO⟩ := s3_fibre_neighborhood p hp y O O.isOpen hKO
  let W : Opens Y := ⟨N, hN⟩ ⊓ U ⊓ V
  have hWU : W ≤ U := fun _ hx => hx.1.2
  have hWV : W ≤ V := inf_le_right
  have hWO : (Opens.map p).obj W ≤ O := fun _ hx => hNO hx.1.1
  refine ⟨W, ⟨⟨hyN, hyU⟩, hyV⟩, hWU, hWV, ?_⟩
  have e := congrArg (F.obj.map (homOfLE hWO).op) he
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at e
  convert e using 1


def s3_fibre_stalk_values {X Y : TopCat} (p : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat X) (y : Y)
    (s : (p _* F.presheaf).stalk y) (x : {x : X // p x = y}) :
    F.presheaf.stalk x.1 :=
  (F.presheaf.stalkPushforward AddCommGrpCat p x.1)
    ((eqToHom (congrArg (fun z => (p _* F.presheaf).stalk z) x.2.symm)) s)

theorem s3_fibre_stalk_values_germ {X Y : TopCat} (p : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat X) (y : Y) (U : Opens Y) (hy : y ∈ U)
    (s : F.obj.obj (op ((Opens.map p).obj U))) (x : {x : X // p x = y}) :
    s3_fibre_stalk_values p F y ((p _* F.presheaf).germ U y hy s) x =
      F.presheaf.germ ((Opens.map p).obj U) x.1
        (show p x.1 ∈ U from x.2.symm ▸ hy) s := by
  rcases x with ⟨x, hx⟩
  subst y
  dsimp only [s3_fibre_stalk_values]
  simpa only [eqToHom_refl, ConcreteCategory.id_apply, ← ConcreteCategory.comp_apply, Category.comp_id]
    using congrArg (fun f => f s) (stalkPushforward_germ AddCommGrpCat p F.presheaf U x hy)

theorem s3_fibre_stalk_values_injective {X Y : TopCat}
    (p : X ⟶ Y) (hp : IsProperMap p) (F : TopCat.Sheaf AddCommGrpCat X) (y : Y) :
    Function.Injective (s3_fibre_stalk_values p F y) := by
  intro a b hab
  obtain ⟨U, hyU, s, rfl⟩ := (p _* F.presheaf).exists_germ_eq a
  obtain ⟨V, hyV, t, rfl⟩ := (p _* F.presheaf).exists_germ_eq b
  obtain ⟨W, hyW, hWU, hWV, he⟩ := s3_fibre_sections_eq_near p hp F y U V hyU hyV s t
    (fun x hx => by
      have h := congrFun hab ⟨x, hx⟩
      simpa only [s3_fibre_stalk_values_germ] using h)
  calc
    _ = (p _* F.presheaf).germ W y hyW
        ((p _* F.presheaf).map (homOfLE hWU).op s) :=
      ((p _* F.presheaf).germ_res_apply (homOfLE hWU) y hyW s).symm
    _ = (p _* F.presheaf).germ W y hyW
        ((p _* F.presheaf).map (homOfLE hWV).op t) := congrArg _ he
    _ = _ := (p _* F.presheaf).germ_res_apply (homOfLE hWV) y hyW t


theorem s3_fibre_stalk_values_range {X Y : TopCat} [T2Space X] [LocallyCompactSpace X]
    (p : X ⟶ Y) (hp : IsProperMap p) (F : TopCat.Sheaf AddCommGrpCat X)
    (y : Y) (g : ∀ x : X, F.presheaf.stalk x) :
    (∃ a : (p _* F.presheaf).stalk y,
      ∀ x : {x : X // p x = y}, s3_fibre_stalk_values p F y a x = g x.1) ↔
    (∀ x, p x = y → ∃ (U : Opens X), x ∈ U ∧ ∃ s : F.obj.obj (op U),
      ∀ z, p z = y → ∀ hz : z ∈ U, F.presheaf.germ U z hz s = g z) := by
  constructor
  · rintro ⟨a, ha⟩ x hx
    obtain ⟨V, hyV, s, rfl⟩ := (p _* F.presheaf).exists_germ_eq a
    refine ⟨(Opens.map p).obj V, (show p x ∈ V from hx.symm ▸ hyV), s, ?_⟩
    intro z hz hzV
    simpa only [s3_fibre_stalk_values_germ] using ha ⟨z, hz⟩
  · intro hg
    obtain ⟨V, hyV, s, hs⟩ := s3_fibre_germs_extend p hp F y g hg
    refine ⟨(p _* F.presheaf).germ V y hyV s, ?_⟩
    rintro ⟨x, hx⟩
    simpa only [s3_fibre_stalk_values_germ] using hs x hx

theorem s3_fibre_stalk_values_unique {X Y : TopCat} [T2Space X] [LocallyCompactSpace X]
    (p : X ⟶ Y) (hp : IsProperMap p) (F : TopCat.Sheaf AddCommGrpCat X)
    (y : Y) (g : ∀ x : X, F.presheaf.stalk x)
    (hg : ∀ x, p x = y → ∃ (U : Opens X), x ∈ U ∧ ∃ s : F.obj.obj (op U),
      ∀ z, p z = y → ∀ hz : z ∈ U, F.presheaf.germ U z hz s = g z) :
    ∃! a : (p _* F.presheaf).stalk y,
      ∀ x : {x : X // p x = y}, s3_fibre_stalk_values p F y a x = g x.1 := by
  obtain ⟨a, ha⟩ := (s3_fibre_stalk_values_range p hp F y g).mpr hg
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply s3_fibre_stalk_values_injective p hp F y
  funext x
  exact (hb x).trans (ha x).symm


def s3_pullback_stalk_iso {X Y : TopCat} (f : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat Y) (x : X) :
    F.presheaf.stalk (f x) ≅
      ((TopCat.Sheaf.pullback AddCommGrpCat f).obj F).presheaf.stalk x := by
  let P := (TopCat.Presheaf.pullback AddCommGrpCat f).obj F.presheaf
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P
  let e := asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P))
  exact TopCat.Presheaf.stalkPullbackIso AddCommGrpCat f F.presheaf x ≪≫ e ≪≫
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapIso
      ((TopCat.Sheaf.forget AddCommGrpCat X).mapIso
        ((TopCat.Sheaf.pullbackIso AddCommGrpCat f).app F))).symm


def s3_pullback_section_map {X Y : TopCat} (f : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat Y) :
    F.presheaf ⟶ f _* ((TopCat.Sheaf.pullback AddCommGrpCat f).obj F).presheaf :=
  (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).unit.app F.presheaf ≫
    (TopCat.Presheaf.pushforward AddCommGrpCat f).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback AddCommGrpCat f).obj F.presheaf) ≫
        ((TopCat.Sheaf.pullbackIso AddCommGrpCat f).app F).inv.hom)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s3_pullback_section_map_germ {X Y : TopCat} (f : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat Y) (x : X) (U : Opens Y) (hx : f x ∈ U) :
    (s3_pullback_section_map f F).app (op U) ≫
      ((TopCat.Sheaf.pullback AddCommGrpCat f).obj F).presheaf.germ
        ((Opens.map f).obj U) x hx =
      F.presheaf.germ U (f x) hx ≫ (s3_pullback_stalk_iso f F x).hom := by
  dsimp only [s3_pullback_section_map, s3_pullback_stalk_iso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_inv, asIso_hom]
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc,
    TopCat.Presheaf.stalkPullbackIso]
  rw [TopCat.Presheaf.germ_stalkPullbackHom_assoc]
  simp only [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc]
  rfl


theorem s3_pullback_section_locally_represented {X Y : TopCat} (i : X ⟶ Y)
    (hi : IsInducing i) (F : TopCat.Sheaf AddCommGrpCat Y)
    (t : ((TopCat.Sheaf.pullback AddCommGrpCat i).obj F).obj.obj (op ⊤))
    (g : ∀ y : Y, F.presheaf.stalk y)
    (hg : ∀ x : X, (s3_pullback_stalk_iso i F x).hom (g (i x)) =
      ((TopCat.Sheaf.pullback AddCommGrpCat i).obj F).presheaf.germ ⊤ x (by trivial) t)
    (x : X) :
    ∃ (U : Opens Y), i x ∈ U ∧ ∃ s : F.obj.obj (op U),
      ∀ z : X, ∀ hz : i z ∈ U, F.presheaf.germ U (i z) hz s = g (i z) := by
  let H := (TopCat.Sheaf.pullback AddCommGrpCat i).obj F
  obtain ⟨U, hxU, s, hs⟩ := F.presheaf.exists_germ_eq (g (i x))
  have he : H.presheaf.germ ((Opens.map i).obj U) x hxU
      ((s3_pullback_section_map i F).app (op U) s) =
      H.presheaf.germ ⊤ x (by trivial) t := by
    calc
      _ = (s3_pullback_stalk_iso i F x).hom (F.presheaf.germ U (i x) hxU s) := by
        exact congrArg (fun f => f s) (s3_pullback_section_map_germ i F x U hxU)
      _ = _ := hs ▸ hg x
  obtain ⟨W, hxW, jU, jT, hst⟩ := H.presheaf.germ_eq x hxU (by trivial) _ t he
  obtain ⟨V, hV, hVW⟩ := hi.isOpen_iff.mp W.isOpen
  let O : Opens Y := U ⊓ ⟨V, hV⟩
  have hxO : i x ∈ O := ⟨hxU, show x ∈ i ⁻¹' V from hVW.symm ▸ hxW⟩
  refine ⟨O, hxO, F.obj.map (homOfLE (inf_le_left : O ≤ U)).op s, ?_⟩
  intro z hz
  have hzW : z ∈ W := by
    change z ∈ (W : Set X)
    rw [← hVW]
    exact hz.2
  apply (ConcreteCategory.bijective_of_isIso (s3_pullback_stalk_iso i F z).hom).1
  rw [F.presheaf.germ_res_apply (homOfLE (inf_le_left : O ≤ U)) (i z) hz s]
  calc
    _ = H.presheaf.germ ((Opens.map i).obj U) z hz.1
        ((s3_pullback_section_map i F).app (op U) s) :=
      (congrArg (fun f => f s) (s3_pullback_section_map_germ i F z U hz.1)).symm
    _ = H.presheaf.germ W z hzW
        (H.presheaf.map jU.op ((s3_pullback_section_map i F).app (op U) s)) :=
      (H.presheaf.germ_res_apply jU z hzW _).symm
    _ = H.presheaf.germ W z hzW (H.presheaf.map jT.op t) := congrArg _ hst
    _ = H.presheaf.germ ⊤ z (by trivial) t := H.presheaf.germ_res_apply jT z hzW t
    _ = _ := (hg z).symm


def s3_fibre_section_map {X Y : TopCat} (p : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat X) (y : Y) (V : Opens Y) (hyV : y ∈ V) :
    F.obj.obj (op ((Opens.map p).obj V)) ⟶
      ((TopCat.Sheaf.pullback AddCommGrpCat (s3_fibreInclusion p y)).obj F).obj.obj (op ⊤) :=
  (s3_pullback_section_map (s3_fibreInclusion p y) F).app (op ((Opens.map p).obj V)) ≫
    ((TopCat.Sheaf.pullback AddCommGrpCat (s3_fibreInclusion p y)).obj F).obj.map
      (homOfLE (show (⊤ : Opens {x : X // p x = y}) ≤
        (Opens.map (s3_fibreInclusion p y)).obj ((Opens.map p).obj V) from
        fun x _ => show p x.1 ∈ V from x.2.symm ▸ hyV)).op

theorem s3_fibre_section_map_germ {X Y : TopCat} (p : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat X) (y : Y) (V : Opens Y) (hyV : y ∈ V)
    (s : F.obj.obj (op ((Opens.map p).obj V))) (x : {x : X // p x = y}) :
    ((TopCat.Sheaf.pullback AddCommGrpCat (s3_fibreInclusion p y)).obj F).presheaf.germ
      ⊤ x (by trivial) (s3_fibre_section_map p F y V hyV s) =
    (s3_pullback_stalk_iso (s3_fibreInclusion p y) F x).hom
      (F.presheaf.germ ((Opens.map p).obj V) x.1
        (show p x.1 ∈ V from x.2.symm ▸ hyV) s) := by
  dsimp only [s3_fibre_section_map]
  rw [ConcreteCategory.comp_apply, TopCat.Presheaf.germ_res_apply]
  exact congrArg (fun f => f s)
    (s3_pullback_section_map_germ (s3_fibreInclusion p y) F x _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s3_fibre_section_extend {X Y : TopCat} [T2Space X] [LocallyCompactSpace X]
    (p : X ⟶ Y) (hp : IsProperMap p) (F : TopCat.Sheaf AddCommGrpCat X) (y : Y)
    (t : ((TopCat.Sheaf.pullback AddCommGrpCat (s3_fibreInclusion p y)).obj F).obj.obj (op ⊤)) :
    ∃ (V : Opens Y) (hyV : y ∈ V) (s : F.obj.obj (op ((Opens.map p).obj V))),
      s3_fibre_section_map p F y V hyV s = t := by
  classical
  let i := s3_fibreInclusion p y
  let H := (TopCat.Sheaf.pullback AddCommGrpCat i).obj F
  let g : ∀ x : X, F.presheaf.stalk x := fun x =>
    if hx : p x = y then
      (s3_pullback_stalk_iso i F ⟨x, hx⟩).inv
        (H.presheaf.germ ⊤ ⟨x, hx⟩ (by trivial) t)
    else 0
  have hg : ∀ x : {x : X // p x = y}, (s3_pullback_stalk_iso i F x).hom (g (i x)) =
      H.presheaf.germ ⊤ x (by trivial) t := by
    rintro ⟨x, hx⟩
    change (s3_pullback_stalk_iso i F ⟨x, hx⟩).hom (g x) = _
    dsimp only [g]
    rw [dite_eq_left hx]
    exact ConcreteCategory.congr_hom ((s3_pullback_stalk_iso i F ⟨x, hx⟩).inv_hom_id) _
  have hlocal : ∀ x, p x = y → ∃ (U : Opens X), x ∈ U ∧ ∃ s : F.obj.obj (op U),
      ∀ z, p z = y → ∀ hz : z ∈ U, F.presheaf.germ U z hz s = g z := by
    intro x hx
    obtain ⟨U, hxU, s, hs⟩ := s3_pullback_section_locally_represented i
      (show IsInducing i from Topology.IsEmbedding.subtypeVal.isInducing) F t g hg ⟨x, hx⟩
    exact ⟨U, hxU, s, fun z hz hzU => hs ⟨z, hz⟩ hzU⟩
  obtain ⟨V, hyV, s, hs⟩ := s3_fibre_germs_extend p hp F y g hlocal
  refine ⟨V, hyV, s, ?_⟩
  apply TopCat.Presheaf.section_ext H ⊤
  intro x _
  rw [s3_fibre_section_map_germ, hs x.1 x.2]
  exact hg x


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s3_fibre_section_eq_near {X Y : TopCat}
    (p : X ⟶ Y) (hp : IsProperMap p) (F : TopCat.Sheaf AddCommGrpCat X)
    (y : Y) (U V : Opens Y) (hyU : y ∈ U) (hyV : y ∈ V)
    (s : F.obj.obj (op ((Opens.map p).obj U)))
    (t : F.obj.obj (op ((Opens.map p).obj V)))
    (h : s3_fibre_section_map p F y U hyU s = s3_fibre_section_map p F y V hyV t) :
    ∃ (W : Opens Y) (_hyW : y ∈ W) (hWU : W ≤ U) (hWV : W ≤ V),
      F.obj.map ((Opens.map p).map (homOfLE hWU)).op s =
        F.obj.map ((Opens.map p).map (homOfLE hWV)).op t := by
  apply s3_fibre_sections_eq_near p hp F y U V hyU hyV s t
  intro x hx
  apply (ConcreteCategory.bijective_of_isIso
    (s3_pullback_stalk_iso (s3_fibreInclusion p y) F ⟨x, hx⟩).hom).1
  have he := congrArg
    (((TopCat.Sheaf.pullback AddCommGrpCat (s3_fibreInclusion p y)).obj F).presheaf.germ
      ⊤ ⟨x, hx⟩ (by trivial)) h
  rw [← s3_fibre_section_map_germ p F y U hyU s ⟨x, hx⟩,
    ← s3_fibre_section_map_germ p F y V hyV t ⟨x, hx⟩]
  exact he

end HodgeLean.Foundations.Program
