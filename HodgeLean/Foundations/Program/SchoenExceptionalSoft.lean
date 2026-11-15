module

public import HodgeLean.Foundations.Program.SchoenExceptionalSections

@[expose] public noncomputable section
open CategoryTheory Topology TopologicalSpace Opposite TopCat.Presheaf
open scoped AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s3_embedding_stalk_family {X Y : TopCat} (i : X ⟶ Y)
    (hi : Function.Injective i) (F : TopCat.Sheaf AddCommGrpCat Y)
    (s : ∀ x : X, ((TopCat.Sheaf.pullback AddCommGrpCat i).obj F).presheaf.stalk x) :
    ∃ g : ∀ y : Y, F.presheaf.stalk y,
      ∀ x : X, (s3_pullback_stalk_iso i F x).hom (g (i x)) = s x := by
  classical
  let g : ∀ y : Y, F.presheaf.stalk y := fun y =>
    if hy : ∃ x : X, i x = y then
      (eqToHom (congrArg (fun z => F.presheaf.stalk z) (Classical.choose_spec hy)))
        ((s3_pullback_stalk_iso i F (Classical.choose hy)).inv (s (Classical.choose hy)))
    else 0
  refine ⟨g, ?_⟩
  intro x
  have h : ∃ z : X, i z = i x := ⟨x, rfl⟩
  have he : ∀ (z : X) (e : i z = i x),
      (eqToHom (congrArg (fun y => F.presheaf.stalk y) e))
          ((s3_pullback_stalk_iso i F z).inv (s z)) =
        (s3_pullback_stalk_iso i F x).inv (s x) := by
    intro z e
    have hz : z = x := hi e
    subst z
    rfl
  dsimp only [g]
  rw [dite_eq_left h, he (Classical.choose h) (Classical.choose_spec h)]
  exact ConcreteCategory.congr_hom (s3_pullback_stalk_iso i F x).inv_hom_id _


theorem s3_pullback_section_locally_represented_onOpen {X Y : TopCat} (i : X ⟶ Y)
    (hi : IsInducing i) (F : TopCat.Sheaf AddCommGrpCat Y)
    (A : Opens X) (t : ((TopCat.Sheaf.pullback AddCommGrpCat i).obj F).obj.obj (op A))
    (g : ∀ y : Y, F.presheaf.stalk y)
    (hg : ∀ (x : X) (hx : x ∈ A), (s3_pullback_stalk_iso i F x).hom (g (i x)) =
      ((TopCat.Sheaf.pullback AddCommGrpCat i).obj F).presheaf.germ A x hx t)
    (x : X) (hxA : x ∈ A) :
    ∃ (U : Opens Y), i x ∈ U ∧ ∃ s : F.obj.obj (op U),
      ∀ z : X, z ∈ A → ∀ hz : i z ∈ U, F.presheaf.germ U (i z) hz s = g (i z) := by
  let H := (TopCat.Sheaf.pullback AddCommGrpCat i).obj F
  obtain ⟨U, hxU, s, hs⟩ := F.presheaf.exists_germ_eq (g (i x))
  have he : H.presheaf.germ ((Opens.map i).obj U) x hxU
      ((s3_pullback_section_map i F).app (op U) s) =
      H.presheaf.germ A x hxA t := by
    calc
      _ = (s3_pullback_stalk_iso i F x).hom (F.presheaf.germ U (i x) hxU s) := by
        exact congrArg (fun f => f s) (s3_pullback_section_map_germ i F x U hxU)
      _ = _ := hs ▸ hg x hxA
  obtain ⟨W, hxW, jU, jT, hst⟩ := H.presheaf.germ_eq x hxU hxA _ t he
  obtain ⟨V, hV, hVW⟩ := hi.isOpen_iff.mp W.isOpen
  let O : Opens Y := U ⊓ ⟨V, hV⟩
  have hxO : i x ∈ O := ⟨hxU, show x ∈ i ⁻¹' V from hVW.symm ▸ hxW⟩
  refine ⟨O, hxO, F.obj.map (homOfLE (inf_le_left : O ≤ U)).op s, ?_⟩
  intro z hzA hz
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
    _ = H.presheaf.germ A z hzA t := H.presheaf.germ_res_apply jT z hzW t
    _ = _ := (hg z hzA).symm


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s3_pullback_isSoft_of_isFlasque {X Y : TopCat} [CompactSpace X] [T2Space X]
    [T2Space Y] [LocallyCompactSpace Y] (i : X ⟶ Y) (hi : IsEmbedding i)
    (F : TopCat.Sheaf AddCommGrpCat Y) [F.IsFlasque] :
    ∀ (K : Set X) (U : Opens X), IsClosed K → K ⊆ U →
      ∀ s : ((TopCat.Sheaf.pullback AddCommGrpCat i).obj F).obj.obj (op U),
        ∃ (V : Opens X) (hV : V ≤ U), K ⊆ V ∧
          ∃ t : ((TopCat.Sheaf.pullback AddCommGrpCat i).obj F).obj.obj (op ⊤),
            ((TopCat.Sheaf.pullback AddCommGrpCat i).obj F).obj.map
                (homOfLE le_top : V ⟶ ⊤).op t =
              ((TopCat.Sheaf.pullback AddCommGrpCat i).obj F).obj.map (homOfLE hV).op s := by
  classical
  intro K U hK hKU t
  let H := (TopCat.Sheaf.pullback AddCommGrpCat i).obj F
  let a : ∀ x : X, H.presheaf.stalk x := fun x =>
    if hx : x ∈ U then H.presheaf.germ U x hx t else 0
  obtain ⟨g, hg⟩ := s3_embedding_stalk_family i hi.injective F a
  have hgU : ∀ (x : X) (hx : x ∈ U),
      (s3_pullback_stalk_iso i F x).hom (g (i x)) = H.presheaf.germ U x hx t := by
    intro x hx
    rw [hg]
    exact dite_eq_left hx
  have hlocal : ∀ y ∈ i '' K, ∃ (O : Opens Y), y ∈ O ∧ ∃ s : F.obj.obj (op O),
      ∀ z ∈ i '' K, ∀ hz : z ∈ O, F.presheaf.germ O z hz s = g z := by
    rintro y ⟨x, hxK, rfl⟩
    obtain ⟨O, hxO, s, hs⟩ := s3_pullback_section_locally_represented_onOpen i
      hi.isInducing F U t g hgU x (hKU hxK)
    refine ⟨O, hxO, s, ?_⟩
    rintro z ⟨w, hwK, rfl⟩ hwO
    exact hs w (hKU hwK) hwO
  obtain ⟨O, hKO, s, hs⟩ := s3_compact_germs_extend Y F (i '' K)
    (hK.isCompact.image i.hom.continuous) g hlocal
  obtain ⟨r, hr⟩ := (AddCommGrpCat.epi_iff_surjective
    (F.obj.map (homOfLE le_top : O ⟶ ⊤).op)).mp
    (TopCat.Presheaf.IsFlasque.epi (homOfLE le_top : O ⟶ ⊤).op) s
  have htop : (⊤ : Opens X) ≤ (Opens.map i).obj ⊤ := fun _ _ => trivial
  let v : H.obj.obj (op ⊤) := H.obj.map (homOfLE htop).op
    ((s3_pullback_section_map i F).app (op ⊤) r)
  have hv : ∀ x (hx : x ∈ K), H.presheaf.germ ⊤ x (by trivial) v =
      H.presheaf.germ U x (hKU hx) t := by
    intro x hx
    dsimp only [v]
    rw [H.presheaf.germ_res_apply]
    calc
      _ = (s3_pullback_stalk_iso i F x).hom (F.presheaf.germ ⊤ (i x) (by trivial) r) :=
        congrArg (fun f => f r) (s3_pullback_section_map_germ i F x ⊤ (by trivial))
      _ = (s3_pullback_stalk_iso i F x).hom (g (i x)) := by
        congr 1
        rw [← F.presheaf.germ_res_apply (homOfLE le_top : O ⟶ ⊤) (i x)
          (hKO ⟨x, hx, rfl⟩) r, hr]
        exact hs (i x) ⟨x, hx, rfl⟩
      _ = _ := hgU x (hKU hx)
  obtain ⟨V, hVT, hVU, hKV, he⟩ := s3_sections_eq_near X H K ⊤ U
    (fun _ _ => trivial) hKU v t hv
  exact ⟨V, hVU, hKV, v, he⟩

end HodgeLean.Foundations.Program
