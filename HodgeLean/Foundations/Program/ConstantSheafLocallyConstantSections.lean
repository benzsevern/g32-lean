import HodgeLean.RealDefs.Port.AlgebraicTopology.Sheaf.MapOfLocalStalks
import Mathlib.Topology.LocallyConstant.Algebra

noncomputable section
open CategoryTheory TopologicalSpace Opposite
universe u
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
/-- The germ of a constant section agrees with the canonical constant stalk map. -/
theorem constantSheafStalkIso_germ
    {X : TopCat.{u}} (A : AddCommGrpCat.{u}) (U : Opens X) (x : X) (hx : x ∈ U) (a : A) :
    𝓒[X; A].presheaf.germ U x hx
      ((toSheafify (Opens.grothendieckTopology X) 𝓒ᵖ[X; A]).app (op U) a) =
      (TopCat.Sheaf.constantSheafStalkIso (X := X) A x).hom a := by
  calc
    _ = ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X) 𝓒ᵖ[X; A]))
          (𝓒ᵖ[X; A].germ U x hx a) :=
      (TopCat.Presheaf.stalkFunctor_map_germ_apply
        (F := 𝓒ᵖ[X; A]) (G := 𝓒[X; A].presheaf) U x hx
        (toSheafify (Opens.grothendieckTopology X) 𝓒ᵖ[X; A]) a).symm
    _ = _ := by
      change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (toSheafify (Opens.grothendieckTopology X) 𝓒ᵖ[X; A]))
            (𝓒ᵖ[X; A].germ U x hx a) =
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (toSheafify (Opens.grothendieckTopology X) 𝓒ᵖ[X; A]))
            (𝓒ᵖ[X; A].Γgerm x a)
      congr 1
      exact (TopCat.Presheaf.Γgerm_res_apply 𝓒ᵖ[X; A] (i := homOfLE (show U ≤ ⊤ from le_top)) x hx a)

set_option backward.isDefEq.respectTransparency false in
/-- Every constant sheaf section has a locally constant function of stalk values. -/
theorem constantSheaf_section_locallyConstant
    {X : TopCat.{u}} (A : AddCommGrpCat.{u}) (U : Opens X)
    (s : 𝓒[X; A].obj.obj (op U)) :
    ∃ f : LocallyConstant U A, ∀ x : U,
      (TopCat.Sheaf.constantSheafStalkIso (X := X) A x).hom (f x) =
        𝓒[X; A].presheaf.germ U x x.property s := by
  let f : U → A := fun x => (TopCat.Sheaf.constantSheafStalkIso (X := X) A x).inv
    (𝓒[X; A].presheaf.germ U x x.property s)
  have hf : ∀ x : U, (TopCat.Sheaf.constantSheafStalkIso (X := X) A x).hom (f x) =
      𝓒[X; A].presheaf.germ U x x.property s := by
    intro x
    change ((TopCat.Sheaf.constantSheafStalkIso (X := X) A x).inv ≫
      (TopCat.Sheaf.constantSheafStalkIso (X := X) A x).hom) _ = _
    rw [Iso.inv_hom_id]
    rfl
  have hlc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    let c := (toSheafify (Opens.grothendieckTopology X) 𝓒ᵖ[X; A]).app (op U) (f x)
    have hc : 𝓒[X; A].presheaf.germ U x x.property s =
        𝓒[X; A].presheaf.germ U x x.property c :=
      (hf x).symm.trans (constantSheafStalkIso_germ A U x x.property (f x)).symm
    obtain ⟨W, hxW, i, j, heq⟩ := 𝓒[X; A].presheaf.germ_eq x x.property x.property s c hc
    have hW : {z : U | (z : X) ∈ W} ∈ nhds x :=
      (W.isOpen.preimage continuous_subtype_val).mem_nhds hxW
    filter_upwards [hW] with z hz
    have hz' : (TopCat.Sheaf.constantSheafStalkIso (X := X) A z).hom (f z) =
        (TopCat.Sheaf.constantSheafStalkIso (X := X) A z).hom (f x) := by
      rw [hf z, ← constantSheafStalkIso_germ A U z z.property (f x)]
      change 𝓒[X; A].presheaf.germ U z z.property s =
        𝓒[X; A].presheaf.germ U z z.property c
      rw [← TopCat.Presheaf.germ_res_apply _ i z hz,
        ← TopCat.Presheaf.germ_res_apply _ j z hz, heq]
    have hv := congrArg (TopCat.Sheaf.constantSheafStalkIso (X := X) A z).inv hz'
    simpa only [← ConcreteCategory.comp_apply, Iso.hom_inv_id,
      ConcreteCategory.id_apply] using hv
  exact ⟨⟨f, hlc⟩, hf⟩

set_option backward.isDefEq.respectTransparency false in
/-- Locally constant functions give unique sections of the sheafified constant sheaf. -/
theorem locallyConstant_unique_constantSheaf_section
    {X : TopCat.{u}} (A : AddCommGrpCat.{u}) (U : Opens X)
    (f : LocallyConstant U A) :
    ∃! s : 𝓒[X; A].obj.obj (op U), ∀ x : U,
      𝓒[X; A].presheaf.germ U x x.property s =
        (TopCat.Sheaf.constantSheafStalkIso (X := X) A x).hom (f x) := by
  let V : U → Opens X := fun x =>
    ⟨Subtype.val '' {z : U | f z = f x},
      (U.isOpen.isOpenMap_subtype_val) _ (f.isLocallyConstant.isOpen_fiber (f x))⟩
  have hVU : ∀ x, V x ≤ U := by
    rintro x z ⟨w, _, rfl⟩
    exact w.property
  have hxV : ∀ x : U, (x : X) ∈ V x := fun x => ⟨x, rfl, rfl⟩
  have hfV : ∀ (x z : U), (z : X) ∈ V x → f z = f x := by
    rintro x z ⟨w, hw, hwz⟩
    have : w = z := Subtype.ext hwz
    simpa only [this, Set.mem_setOf_eq] using hw
  let s : ∀ x : U, 𝓒[X; A].obj.obj (op (V x)) := fun x =>
    (toSheafify (Opens.grothendieckTopology X) 𝓒ᵖ[X; A]).app (op (V x)) (f x)
  have hc : TopCat.Presheaf.IsCompatible 𝓒[X; A].obj V s := by
    intro x z
    apply TopCat.Presheaf.section_ext 𝓒[X; A]
    intro w hw
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    change 𝓒[X; A].presheaf.germ (V x) w hw.1 (s x) =
      𝓒[X; A].presheaf.germ (V z) w hw.2 (s z)
    rw [constantSheafStalkIso_germ, constantSheafStalkIso_germ]
    congr 1
    exact (hfV x ⟨w, hVU x hw.1⟩ hw.1).symm.trans
      (hfV z ⟨w, hVU x hw.1⟩ hw.2)
  have hcover : U ≤ iSup V := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨r, hr, _⟩ := 𝓒[X; A].existsUnique_gluing' V U
    (fun x => homOfLE (hVU x)) hcover s hc
  have hg : ∀ x : U, 𝓒[X; A].presheaf.germ U x x.property r =
      (TopCat.Sheaf.constantSheafStalkIso (X := X) A x).hom (f x) := by
    intro x
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (hVU x)) x (hxV x), hr x]
    exact constantSheafStalkIso_germ A (V x) x (hxV x) (f x)
  refine ⟨r, hg, ?_⟩
  intro r' hr'
  apply TopCat.Presheaf.section_ext 𝓒[X; A]
  intro x hx
  exact (hr' ⟨x, hx⟩).trans (hg ⟨x, hx⟩).symm

set_option backward.isDefEq.respectTransparency false in
/-- The additive identification of constant sheaf sections with locally constant functions. -/
def constantSheafSectionEquiv
    {X : TopCat.{u}} (A : AddCommGrpCat.{u}) (U : Opens X) :
    𝓒[X; A].obj.obj (op U) ≃+ LocallyConstant U A where
  toFun s := (constantSheaf_section_locallyConstant A U s).choose
  invFun f := (locallyConstant_unique_constantSheaf_section A U f).exists.choose
  left_inv s := by
    apply TopCat.Presheaf.section_ext 𝓒[X; A]
    intro x hx
    exact ((locallyConstant_unique_constantSheaf_section A U
      (constantSheaf_section_locallyConstant A U s).choose).exists.choose_spec ⟨x, hx⟩).trans
      ((constantSheaf_section_locallyConstant A U s).choose_spec ⟨x, hx⟩)
  right_inv f := by
    apply LocallyConstant.ext
    intro x
    have h := (constantSheaf_section_locallyConstant A U
      (locallyConstant_unique_constantSheaf_section A U f).exists.choose).choose_spec x
    rw [(locallyConstant_unique_constantSheaf_section A U f).exists.choose_spec x] at h
    have h' := congrArg (TopCat.Sheaf.constantSheafStalkIso (X := X) A x).inv h
    simpa only [← ConcreteCategory.comp_apply, Iso.hom_inv_id,
      ConcreteCategory.id_apply] using h'
  map_add' s t := by
    apply LocallyConstant.ext
    intro x
    have h := (constantSheaf_section_locallyConstant A U (s + t)).choose_spec x
    rw [map_add, ← (constantSheaf_section_locallyConstant A U s).choose_spec x,
      ← (constantSheaf_section_locallyConstant A U t).choose_spec x] at h
    have h' := congrArg (TopCat.Sheaf.constantSheafStalkIso (X := X) A x).inv h
    simpa only [LocallyConstant.add_apply, map_add, ← ConcreteCategory.comp_apply, Iso.hom_inv_id,
      ConcreteCategory.id_apply] using h'

/-- The section identification retains the specified stalk values. -/
theorem constantSheafSectionEquiv_germ
    {X : TopCat.{u}} (A : AddCommGrpCat.{u}) (U : Opens X)
    (s : 𝓒[X; A].obj.obj (op U)) (x : U) :
    (TopCat.Sheaf.constantSheafStalkIso (X := X) A x).hom
        (constantSheafSectionEquiv A U s x) =
      𝓒[X; A].presheaf.germ U x x.property s :=
  (constantSheaf_section_locallyConstant A U s).choose_spec x

set_option backward.isDefEq.respectTransparency false in
/-- The section identification commutes with restrictions to open subsets. -/
theorem constantSheafSectionEquiv_restrict
    {X : TopCat.{u}} (A : AddCommGrpCat.{u}) (U V : Opens X) (hle : V ≤ U)
    (s : 𝓒[X; A].obj.obj (op U)) (x : V) :
    constantSheafSectionEquiv A V
        (𝓒[X; A].obj.map (homOfLE hle).op s) x =
      constantSheafSectionEquiv A U s ⟨x, hle x.property⟩ := by
  have h : (TopCat.Sheaf.constantSheafStalkIso (X := X) A x).hom
      (constantSheafSectionEquiv A V (𝓒[X; A].obj.map (homOfLE hle).op s) x) =
      (TopCat.Sheaf.constantSheafStalkIso (X := X) A x).hom
        (constantSheafSectionEquiv A U s ⟨x, hle x.property⟩) := by
    exact (constantSheafSectionEquiv_germ A V _ x).trans
      ((TopCat.Presheaf.germ_res_apply 𝓒[X; A].presheaf
        (homOfLE hle) x x.property s).trans
          (constantSheafSectionEquiv_germ A U s ⟨x, hle x.property⟩).symm)
  have h' := congrArg (TopCat.Sheaf.constantSheafStalkIso (X := X) A x).inv h
  simpa only [← ConcreteCategory.comp_apply, Iso.hom_inv_id,
    ConcreteCategory.id_apply] using h'

set_option backward.isDefEq.respectTransparency false in
/-- Actual constant sections correspond to constant functions. -/
theorem constantSheafSectionEquiv_constant
    {X : TopCat.{u}} (A : AddCommGrpCat.{u}) (U : Opens X) (a : A) (x : U) :
    constantSheafSectionEquiv A U
      ((toSheafify (Opens.grothendieckTopology X) 𝓒ᵖ[X; A]).app (op U) a) x = a := by
  have h := (constantSheafSectionEquiv_germ A U
    ((toSheafify (Opens.grothendieckTopology X) 𝓒ᵖ[X; A]).app (op U) a) x).trans
      (constantSheafStalkIso_germ A U x x.property a)
  have h' := congrArg (TopCat.Sheaf.constantSheafStalkIso (X := X) A x).inv h
  simpa only [← ConcreteCategory.comp_apply, Iso.hom_inv_id,
    ConcreteCategory.id_apply] using h'

end HodgeLean.Foundations.Program
