import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Forget
import HodgeLean.Foundations.Program.SchoenTransferQuotientStalks

/-! Rational transfer on the opens of an actual quotient. -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program

/-- The given action restricts to the inverse image of a quotient open. -/
@[instance_reducible] def s4_quotient_openAction
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Group G] [MulAction G X] (f : C(X, Y))
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) (U : Opens Y) :
    MulAction G {x : X // f x ∈ U} where
  smul g x := ⟨g • x.val, by rw [hfg]; exact x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

/-- Restricted quotient actions remain continuous. -/
theorem s4_quotient_openAction_continuous
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Group G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (f : C(X, Y))
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) (U : Opens Y) :
    letI := s4_quotient_openAction f hfg U
    ∀ g : G, Continuous (fun x : {x : X // f x ∈ U} => g • x) := by
  letI := s4_quotient_openAction f hfg U
  intro g
  exact ((hc g).comp continuous_subtype_val).subtype_mk _

/-- The restricted action still exhausts each quotient fibre. -/
theorem s4_quotient_open_orbits
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Group G] [MulAction G X] (f : C(X, Y))
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) (U : Opens Y) :
    letI := s4_quotient_openAction f hfg U
    ∀ x y : {x : X // f x ∈ U},
      (f.restrictPreimage (U : Set Y)) x = (f.restrictPreimage (U : Set Y)) y →
        ∃ g : G, g • x = y := by
  letI := s4_quotient_openAction f hfg U
  intro x y hxy
  obtain ⟨g, hg⟩ := horb x.val y.val (congrArg Subtype.val hxy)
  exact ⟨g, Subtype.ext hg⟩

/-- Normalized rational transfer on every open of the quotient. -/
def s4_quotient_openTransfer
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (f : C(X, Y))
    (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) (U : Opens Y) :
    LocallyConstant {x : X // f x ∈ U} ℚ →ₗ[ℚ] LocallyConstant U ℚ := by
  letI := s4_quotient_openAction f hfg U
  exact s4_quotient_sectionTransfer (s4_quotient_openAction_continuous hc f hfg U)
    (f.restrictPreimage (U : Set Y)) (hf.restrictPreimage_isOpen U.isOpen)
    (s4_quotient_open_orbits f horb hfg U)

/-- Normalized transfer commutes with restriction between quotient opens. -/
theorem s4_quotient_openTransfer_restrict
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (f : C(X, Y))
    (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x)
    (U V : Opens Y) (hUV : U ≤ V) :
    let i : C({x : X // f x ∈ U}, {x : X // f x ∈ V}) :=
      ⟨fun x => ⟨x.val, hUV x.property⟩, continuous_subtype_val.subtype_mk _⟩
    let j : C(U, V) :=
      ⟨fun x => ⟨x.val, hUV x.property⟩, continuous_subtype_val.subtype_mk _⟩
    (s4_quotient_openTransfer hc f hf horb hfg U).comp (LocallyConstant.comapₗ ℚ i) =
      (LocallyConstant.comapₗ ℚ j).comp (s4_quotient_openTransfer hc f hf horb hfg V) := by
  letI := s4_quotient_openAction f hfg U
  letI := s4_quotient_openAction f hfg V
  exact s4_quotient_sectionTransfer_naturality
    (s4_quotient_openAction_continuous hc f hfg V)
    (s4_quotient_openAction_continuous hc f hfg U)
    (f.restrictPreimage (V : Set Y)) (f.restrictPreimage (U : Set Y))
    (hf.restrictPreimage_isOpen V.isOpen) (hf.restrictPreimage_isOpen U.isOpen)
    (s4_quotient_open_orbits f horb hfg V) (s4_quotient_open_orbits f horb hfg U)
    ⟨fun x => ⟨x.val, hUV x.property⟩, continuous_subtype_val.subtype_mk _⟩
    ⟨fun x => ⟨x.val, hUV x.property⟩, continuous_subtype_val.subtype_mk _⟩
    (fun _ => rfl) (fun _ _ => rfl)

/-- The presheaf of actual locally constant rational functions. -/
def s4_locallyConstantPresheaf (X : TopCat.{0}) : TopCat.Presheaf AddCommGrpCat.{0} X where
  obj U := AddCommGrpCat.of (LocallyConstant U.unop ℚ)
  map {U V} i := AddCommGrpCat.ofHom (LocallyConstant.comapAddMonoidHom
    ⟨fun x => ⟨x.val, i.unop.le x.property⟩, continuous_subtype_val.subtype_mk _⟩)
  map_id _ := by ext u x; rfl
  map_comp _ _ := by ext u x; rfl

/-- The open transfers form an actual morphism of rational section presheaves. -/
def s4_quotient_transferPresheaf
    {X Y : TopCat.{0}} {G : Type*} [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (f : C(X, Y))
    (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) :
    (TopCat.Presheaf.pushforward AddCommGrpCat (TopCat.ofHom f)).obj
      (s4_locallyConstantPresheaf X) ⟶ s4_locallyConstantPresheaf Y where
  app U := AddCommGrpCat.ofHom (s4_quotient_openTransfer hc f hf horb hfg U.unop).toAddMonoidHom
  naturality {U V} i := by
    have h := s4_quotient_openTransfer_restrict hc f hf horb hfg V.unop U.unop i.unop.le
    ext u
    exact LinearMap.congr_fun h u

/-- Locally constant rational functions satisfy the actual sheaf condition. -/
theorem s4_locallyConstantPresheaf_isSheaf (X : TopCat.{0}) :
    (s4_locallyConstantPresheaf X).IsSheaf := by
  letI : TopologicalSpace ℚ := ⊥
  letI : DiscreteTopology ℚ := ⟨rfl⟩
  have e : s4_locallyConstantPresheaf X ⋙ forget AddCommGrpCat ≅
      TopCat.presheafToTop X (TopCat.of ℚ) := by
    refine NatIso.ofComponents (fun U => ?_) ?_
    · exact
        { hom := ↾fun (u : LocallyConstant U.unop ℚ) => TopCat.ofHom ⟨u.toFun, u.continuous⟩
          inv := ↾fun (u : TopCat.of U.unop ⟶ TopCat.of ℚ) =>
            ⟨u.hom.toFun, (IsLocallyConstant.iff_continuous _).mpr u.hom.continuous⟩
          hom_inv_id := by ext u; rfl
          inv_hom_id := by ext u; rfl }
    · intro U V i
      ext u
      rfl
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)
    (s4_locallyConstantPresheaf X)).mpr
  exact TopCat.Presheaf.isSheaf_of_iso e.symm
    (TopCat.sheafToTop (X := X) (TopCat.of ℚ)).property

/-- The abelian sheaf of actual locally constant rational functions. -/
def s4_locallyConstantSheaf (X : TopCat.{0}) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  ⟨s4_locallyConstantPresheaf X, s4_locallyConstantPresheaf_isSheaf X⟩

/-- Normalized transfer is a morphism of the actual abelian section sheaves. -/
def s4_quotient_transferSheaf
    {X Y : TopCat.{0}} {G : Type*} [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (f : C(X, Y))
    (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) :
    (TopCat.Sheaf.pushforward AddCommGrpCat (TopCat.ofHom f)).obj
      (s4_locallyConstantSheaf X) ⟶ s4_locallyConstantSheaf Y :=
  ⟨s4_quotient_transferPresheaf hc f hf horb hfg⟩

/-- Quotient pullback is composition of actual rational section functions. -/
def s4_quotient_pullbackPresheaf
    {X Y : TopCat.{0}} (f : C(X, Y)) :
    s4_locallyConstantPresheaf Y ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat (TopCat.ofHom f)).obj
        (s4_locallyConstantPresheaf X) where
  app U := AddCommGrpCat.ofHom
    (LocallyConstant.comapAddMonoidHom (Z := ℚ) (f.restrictPreimage (U.unop : Set Y)))
  naturality {U V} i := by ext u; rfl

/-- The actual rational-section sheaf pullback into direct image. -/
def s4_quotient_pullbackSheaf
    {X Y : TopCat.{0}} (f : C(X, Y)) :
    s4_locallyConstantSheaf Y ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat (TopCat.ofHom f)).obj
        (s4_locallyConstantSheaf X) :=
  ⟨s4_quotient_pullbackPresheaf f⟩

/-- Transfer retracts actual quotient pullback separately on every open. -/
theorem s4_quotient_openTransfer_retraction
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (f : C(X, Y))
    (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) (U : Opens Y) :
    (s4_quotient_openTransfer hc f hf horb hfg U).comp
      (LocallyConstant.comapₗ ℚ (f.restrictPreimage (U : Set Y))) = LinearMap.id := by
  letI := s4_quotient_openAction f hfg U
  exact s4_quotient_sectionTransfer_retraction
    (s4_quotient_openAction_continuous hc f hfg U) (f.restrictPreimage (U : Set Y))
    (hf.restrictPreimage_isOpen U.isOpen) (s4_quotient_open_orbits f horb hfg U)
    (fun g x => Subtype.ext (hfg g x.val))

/-- Normalized sheaf transfer splits the actual quotient pullback. -/
theorem s4_quotient_sheaf_retraction
    {X Y : TopCat.{0}} {G : Type*} [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (f : C(X, Y))
    (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) :
    s4_quotient_pullbackSheaf f ≫ s4_quotient_transferSheaf hc f hf horb hfg =
      𝟙 (s4_locallyConstantSheaf Y) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext u
  exact LinearMap.congr_fun (s4_quotient_openTransfer_retraction hc f hf horb hfg U.unop) u

/-- Pullback by a deck transformation on the actual direct-image sheaf. -/
def s4_quotient_deckSheaf
    {X Y : TopCat.{0}} {G : Type*} [Group G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (f : C(X, Y))
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) (g : G) :
    (TopCat.Sheaf.pushforward AddCommGrpCat (TopCat.ofHom f)).obj
      (s4_locallyConstantSheaf X) ⟶
    (TopCat.Sheaf.pushforward AddCommGrpCat (TopCat.ofHom f)).obj
      (s4_locallyConstantSheaf X) where
  hom :=
    { app U := by
        letI := s4_quotient_openAction f hfg U.unop
        exact AddCommGrpCat.ofHom (LocallyConstant.comapAddMonoidHom (Z := ℚ)
          ⟨fun x : {x : X // f x ∈ U.unop} => g • x,
            s4_quotient_openAction_continuous hc f hfg U.unop g⟩)
      naturality {U V} i := by ext u; rfl }

/-- Actual quotient sheaf pullback is fixed by every deck endomorphism. -/
theorem s4_quotient_pullbackSheaf_fixed
    {X Y : TopCat.{0}} {G : Type*} [Group G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (f : C(X, Y))
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) (g : G) :
    s4_quotient_pullbackSheaf f ≫ s4_quotient_deckSheaf hc f hfg g =
      s4_quotient_pullbackSheaf f := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext u
  change LocallyConstant U.unop ℚ at u
  apply LocallyConstant.ext
  intro x
  exact congrArg (fun y : U.unop => u y) (Subtype.ext (hfg g x.val))

/-- Every invariant morphism factors uniquely through the actual quotient sheaf pullback. -/
theorem s4_quotient_invariantSheaf_lift
    {X Y : TopCat.{0}} {G : Type*} [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (f : C(X, Y))
    (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x)
    (A : TopCat.Sheaf AddCommGrpCat.{0} Y)
    (h : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat (TopCat.ofHom f)).obj
      (s4_locallyConstantSheaf X))
    (hh : ∀ g : G, h ≫ s4_quotient_deckSheaf hc f hfg g = h) :
    ∃! k : A ⟶ s4_locallyConstantSheaf Y, k ≫ s4_quotient_pullbackSheaf f = h := by
  refine ⟨h ≫ s4_quotient_transferSheaf hc f hf horb hfg, ?_, ?_⟩
  · apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    ext u
    letI := s4_quotient_openAction f hfg U.unop
    let fU := f.restrictPreimage (U.unop : Set Y)
    let w : LocallyConstant {x : X // f x ∈ U.unop} ℚ := h.hom.app U u
    have hw : ∀ x y, fU x = fU y → w x = w y := by
      intro x y hxy
      obtain ⟨g, hg⟩ := s4_quotient_open_orbits f horb hfg U.unop x y hxy
      have he := congrArg (fun z => z.hom.app U) (hh g)
      have he' := ConcreteCategory.congr_hom he u
      rw [← hg]
      exact (congrArg (fun v : LocallyConstant {x : X // f x ∈ U.unop} ℚ => v x) he').symm
    obtain ⟨v, hv, _⟩ := s4_locallyConstant_quotient_descent fU
      (hf.restrictPreimage_isOpen U.unop.isOpen) w hw
    have hp : LocallyConstant.comapₗ ℚ fU v = w := LocallyConstant.ext hv
    change LocallyConstant.comapₗ ℚ fU
      (s4_quotient_openTransfer hc f hf horb hfg U.unop w) = w
    rw [← hp]
    exact congrArg (LocallyConstant.comapₗ ℚ fU)
      (LinearMap.congr_fun (s4_quotient_openTransfer_retraction hc f hf horb hfg U.unop) v)
  · intro k hk
    have he := congrArg (fun z => z ≫ s4_quotient_transferSheaf hc f hf horb hfg) hk
    simpa only [Category.assoc, s4_quotient_sheaf_retraction, Category.comp_id] using he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The split quotient sheaf pullback is injective in every cohomology degree. -/
theorem s4_quotient_sheafCohomology_injective
    {X Y : TopCat.{0}} {G : Type*} [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (f : C(X, Y))
    (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) (n : ℕ) :
    let E := (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift ℤ))
    Function.Injective ((Abelian.extFunctorObj E n).map (s4_quotient_pullbackSheaf f)) := by
  let E := (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift ℤ))
  let H := Abelian.extFunctorObj E n
  have he := congrArg H.map (s4_quotient_sheaf_retraction hc f hf horb hfg)
  rw [H.map_comp (s4_quotient_pullbackSheaf f)
    (s4_quotient_transferSheaf hc f hf horb hfg), H.map_id (s4_locallyConstantSheaf Y)] at he
  have hl : Function.LeftInverse
      (H.map (s4_quotient_transferSheaf hc f hf horb hfg))
      (H.map (s4_quotient_pullbackSheaf f)) := by
    intro a
    have h := ConcreteCategory.congr_hom he a
    exact h
  exact hl.injective

/-- Actual constant sections give the comparison from the constant presheaf. -/
def s4_constant_sectionMap (X : TopCat.{0}) :
    (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of ℚ) ⟶
      s4_locallyConstantPresheaf X where
  app U := AddCommGrpCat.ofHom (LocallyConstant.constAddMonoidHom (X := U.unop) (Y := ℚ))
  naturality {U V} i := by ext a; rfl

/-- The constant-section comparison is locally injective. -/
theorem s4_constant_sectionMap_locallyInjective (X : TopCat.{0}) :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (s4_constant_sectionMap X) := by
  constructor
  intro U a b hab x hx
  refine ⟨U.unop, 𝟙 _, ?_, hx⟩
  change a = b
  exact congrArg (fun v : LocallyConstant U.unop ℚ => v ⟨x, hx⟩) hab

/-- Locally constant sections are locally actual constant sections. -/
theorem s4_constant_sectionMap_locallySurjective (X : TopCat.{0}) :
    TopCat.Presheaf.IsLocallySurjective (s4_constant_sectionMap X) := by
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro U u x hx
  change LocallyConstant U ℚ at u
  let c : ℚ := u ⟨x, hx⟩
  let V : Opens X := ⟨Subtype.val '' (u ⁻¹' {c}),
    U.isOpenEmbedding.isOpenMap _ (u.isLocallyConstant.isOpen_fiber c)⟩
  have hVU : V ≤ U := by
    rintro y ⟨z, _, rfl⟩
    exact z.property
  have hxV : x ∈ V := ⟨⟨x, hx⟩, rfl, rfl⟩
  refine ⟨V, hVU, ⟨c, ?_⟩, hxV⟩
  apply LocallyConstant.ext
  intro y
  obtain ⟨z, hz, hzy⟩ := y.property
  have he : z = (⟨y.val, hVU y.property⟩ : U) := Subtype.ext hzy
  change c = u ⟨y.val, hVU y.property⟩
  rw [← he]
  exact hz.symm

/-- Sheafification of the canonical constant-section comparison is invertible. -/
theorem s4_constant_sectionMap_sheafification_isIso (X : TopCat.{0}) :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
      (s4_constant_sectionMap X)) := by
  apply ((Opens.grothendieckTopology X).W_iff _).mp
  exact ((Opens.grothendieckTopology X).W_iff_isLocallyBijective _).mpr
    ⟨s4_constant_sectionMap_locallyInjective X, s4_constant_sectionMap_locallySurjective X⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical identification of the constant rational sheaf with actual sections. -/
def s4_constantSheaf_locallyConstantIso (X : TopCat.{0}) :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
      (AddCommGrpCat.of ℚ) ≅ s4_locallyConstantSheaf X := by
  letI := s4_constant_sectionMap_sheafification_isIso X
  exact asIso ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
    (s4_constant_sectionMap X)) ≪≫
    asIso ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).counit.app
      (s4_locallyConstantSheaf X))

/-- The actual deck sum equals the group order times the normalized sheaf projector. -/
theorem s4_quotient_sheaf_projector_sum
    {X Y : TopCat.{0}} {G : Type*} [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (f : C(X, Y))
    (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) :
    Fintype.card G • (s4_quotient_transferSheaf hc f hf horb hfg ≫
      s4_quotient_pullbackSheaf f) = ∑ g : G, s4_quotient_deckSheaf hc f hfg g := by
  classical
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext u
  change LocallyConstant {x : X // f x ∈ U.unop} ℚ at u
  apply LocallyConstant.ext
  intro x
  change {x : X // f x ∈ U.unop} at x
  let Q := (TopCat.Sheaf.pushforward AddCommGrpCat (TopCat.ofHom f)).obj
    (s4_locallyConstantSheaf X)
  let ev : (Q ⟶ Q) →+ ℚ :=
    { toFun := fun m => LocallyConstant.toFun (m.hom.app U u) x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (Fintype.card G • _) = ev (∑ g : G, _)
  rw [map_nsmul, map_sum]
  letI := s4_quotient_openAction f hfg U.unop
  have he := congrArg (fun v : LocallyConstant {x : X // f x ∈ U.unop} ℚ => v x)
    (s4_quotient_sectionTransfer_pullback
      (s4_quotient_openAction_continuous hc f hfg U.unop)
      (f.restrictPreimage (U.unop : Set Y))
      (hf.restrictPreimage_isOpen U.unop.isOpen)
      (s4_quotient_open_orbits f horb hfg U.unop) u)
  change Fintype.card G •
    (LocallyConstant.comapₗ ℚ (f.restrictPreimage (U.unop : Set Y))
      (s4_quotient_openTransfer hc f hf horb hfg U.unop u)) x =
    ∑ g : G, u (g • x)
  dsimp only [s4_quotient_openTransfer]
  rw [he, s4_locallyConstant_average_apply, nsmul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

/-- Nonzero integer multiplication is invertible on the rational section sheaf. -/
theorem s4_locallyConstantSheaf_nsmul_isIso (X : TopCat.{0}) (n : ℕ) (hn : n ≠ 0) :
    IsIso (n • 𝟙 (s4_locallyConstantSheaf X)) := by
  let v : s4_locallyConstantSheaf X ⟶ s4_locallyConstantSheaf X :=
    { hom :=
        { app := fun U => AddCommGrpCat.ofHom
            { toFun := fun (u : LocallyConstant U.unop ℚ) => (n : ℚ)⁻¹ • u
              map_zero' := smul_zero _
              map_add' := smul_add _ }
          naturality := fun {U V} i => by ext u; rfl } }
  refine ⟨⟨v, ?_, ?_⟩⟩
  · apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    ext u
    change LocallyConstant U.unop ℚ at u
    apply LocallyConstant.ext
    intro x
    change (n : ℚ)⁻¹ * (n • u x) = u x
    rw [nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]
  · apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    ext u
    change LocallyConstant U.unop ℚ at u
    apply LocallyConstant.ext
    intro x
    change n • ((n : ℚ)⁻¹ * u x) = u x
    rw [nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Nonzero integer multiplication stays invertible under rational-section direct image. -/
theorem s4_locallyConstant_pushforward_nsmul_isIso
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (hn : n ≠ 0) :
    IsIso (n • 𝟙 ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj
      (s4_locallyConstantSheaf X))) := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat f
  letI : P.Additive := Functor.additive_of_preserves_binary_products P
  letI := s4_locallyConstantSheaf_nsmul_isIso X n hn
  have hi : IsIso (P.map (n • 𝟙 (s4_locallyConstantSheaf X))) := inferInstance
  rw [P.map_nsmul, P.map_id (s4_locallyConstantSheaf X)] at hi
  exact hi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every deck-invariant higher extension class has a unique normalized quotient lift. -/
theorem s4_quotient_ext_invariant_lift
    {X Y : TopCat.{0}} {G : Type*} [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (f : C(X, Y))
    (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x)
    (E : TopCat.Sheaf AddCommGrpCat.{0} Y) (n : ℕ)
    (a : (Abelian.extFunctorObj E n).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat (TopCat.ofHom f)).obj
        (s4_locallyConstantSheaf X)))
    (ha : ∀ g : G, (Abelian.extFunctorObj E n).map
      (s4_quotient_deckSheaf hc f hfg g) a = a) :
    ∃! b : (Abelian.extFunctorObj E n).obj (s4_locallyConstantSheaf Y),
      (Abelian.extFunctorObj E n).map (s4_quotient_pullbackSheaf f) b = a := by
  classical
  let Q := (TopCat.Sheaf.pushforward AddCommGrpCat (TopCat.ofHom f)).obj
    (s4_locallyConstantSheaf X)
  let H := Abelian.extFunctorObj E n
  let P := s4_quotient_pullbackSheaf f
  let T := s4_quotient_transferSheaf hc f hf horb hfg
  let ev : (Q ⟶ Q) →+ H.obj Q :=
    { toFun := fun m => H.map m a
      map_zero' := by simp
      map_add' := by intro m m'; simp [Functor.map_add, AddCommGrpCat.hom_add_apply] }
  have hs := congrArg ev (s4_quotient_sheaf_projector_sum hc f hf horb hfg)
  rw [map_nsmul, map_sum] at hs
  change Fintype.card G • H.map (T ≫ P) a =
    ∑ g : G, H.map (s4_quotient_deckSheaf hc f hfg g) a at hs
  rw [H.map_comp T P] at hs
  have he : Fintype.card G • H.map P (H.map T a) = Fintype.card G • a := by
    calc
      _ = ∑ g : G, H.map (s4_quotient_deckSheaf hc f hfg g) a := by
        exact hs
      _ = ∑ _g : G, a := Finset.sum_congr rfl (fun g _ => ha g)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ]
  letI := s4_locallyConstant_pushforward_nsmul_isIso
    (TopCat.ofHom f) (Fintype.card G) Fintype.card_ne_zero
  have hi : Function.Injective (H.map (Fintype.card G • 𝟙 Q)) :=
    AddCommGrpCat.injective_of_mono _
  have hPa : H.map P (H.map T a) = a := by
    apply hi
    rw [H.map_nsmul, H.map_id Q]
    exact he
  refine ⟨H.map T a, hPa, ?_⟩
  intro b hb
  have hr := congrArg H.map (s4_quotient_sheaf_retraction hc f hf horb hfg)
  rw [H.map_comp P T, H.map_id (s4_locallyConstantSheaf Y)] at hr
  have he' := ConcreteCategory.congr_hom hr b
  change H.map T (H.map P b) = b at he'
  rw [hb] at he'
  exact he'.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The higher-extension pullback image consists exactly of the actual deck invariants. -/
theorem s4_quotient_ext_invariant_range
    {X Y : TopCat.{0}} {G : Type*} [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x)) (f : C(X, Y))
    (hf : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x)
    (E : TopCat.Sheaf AddCommGrpCat.{0} Y) (n : ℕ)
    (a : (Abelian.extFunctorObj E n).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat (TopCat.ofHom f)).obj
        (s4_locallyConstantSheaf X))) :
    (∃ b : (Abelian.extFunctorObj E n).obj (s4_locallyConstantSheaf Y),
      (Abelian.extFunctorObj E n).map (s4_quotient_pullbackSheaf f) b = a) ↔
    ∀ g : G, (Abelian.extFunctorObj E n).map
      (s4_quotient_deckSheaf hc f hfg g) a = a := by
  constructor
  · rintro ⟨b, rfl⟩ g
    let H := Abelian.extFunctorObj E n
    have he := congrArg H.map (s4_quotient_pullbackSheaf_fixed hc f hfg g)
    rw [H.map_comp] at he
    exact ConcreteCategory.congr_hom he b
  · intro ha
    obtain ⟨b, hb, _⟩ := s4_quotient_ext_invariant_lift hc f hf horb hfg E n a ha
    exact ⟨b, hb⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The coefficient identification sends the canonical presheaf unit to actual constant sections. -/
theorem s4_constantSheaf_locallyConstantIso_unit (X : TopCat.{0}) :
    toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of ℚ)) ≫
      (s4_constantSheaf_locallyConstantIso X).hom.hom = s4_constant_sectionMap X := by
  change toSheafify (Opens.grothendieckTopology X) _ ≫
    (sheafifyMap (Opens.grothendieckTopology X) (s4_constant_sectionMap X) ≫
      ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).counit.app
        (s4_locallyConstantSheaf X)).hom) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    sheafificationAdjunction_counit_app_val, toSheafify_sheafifyLift]
  exact Category.comp_id (s4_constant_sectionMap X)

attribute [local instance] Abelian.Ext.instAddCommGroup

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Actual section pullback followed by the finite-map sheaf-cohomology comparison. -/
def s4_finite_sheafCohomologyPullback
    {X Y : TopCat.{0}} [T2Space X] (f : C(X, Y)) (hf : IsClosedMap f)
    (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} (s4_locallyConstantSheaf Y) n →+
      CategoryTheory.Sheaf.H.{0} (s4_locallyConstantSheaf X) n :=
  (s4_finite_closed_sheafCohomologyEquiv (TopCat.ofHom f) hf hfin
    (s4_locallyConstantSheaf X) n).toAddMonoidHom.comp
      (CategoryTheory.Sheaf.H.map (s4_quotient_pullbackSheaf f) n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Normalized rational sheaf transfer from source cohomology to quotient cohomology. -/
def s4_finite_sheafCohomologyTransfer
    {X Y : TopCat.{0}} [T2Space X] {G : Type*}
    [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x))
    (f : C(X, Y)) (hf : IsClosedMap f)
    (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite) (hq : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} (s4_locallyConstantSheaf X) n →+
      CategoryTheory.Sheaf.H.{0} (s4_locallyConstantSheaf Y) n :=
  (CategoryTheory.Sheaf.H.map (s4_quotient_transferSheaf hc f hq horb hfg) n).comp
    (s4_finite_closed_sheafCohomologyEquiv (TopCat.ofHom f) hf hfin
      (s4_locallyConstantSheaf X) n).symm.toAddMonoidHom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Normalized finite quotient transfer retracts pullback on source and base cohomology. -/
theorem s4_finite_sheafCohomology_retraction
    {X Y : TopCat.{0}} [T2Space X] {G : Type*}
    [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x))
    (f : C(X, Y)) (hf : IsClosedMap f)
    (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite) (hq : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) (n : ℕ) :
    (s4_finite_sheafCohomologyTransfer hc f hf hfin hq horb hfg n).comp
      (s4_finite_sheafCohomologyPullback f hf hfin n) = AddMonoidHom.id _ := by
  ext z
  let e := s4_finite_closed_sheafCohomologyEquiv (TopCat.ofHom f) hf hfin
    (s4_locallyConstantSheaf X) n
  change CategoryTheory.Sheaf.H.map (s4_quotient_transferSheaf hc f hq horb hfg) n
    (e.symm (e (CategoryTheory.Sheaf.H.map (s4_quotient_pullbackSheaf f) n z))) = z
  rw [e.symm_apply_apply, ← CategoryTheory.Sheaf.H.map_comp_apply,
    s4_quotient_sheaf_retraction, CategoryTheory.Sheaf.H.map_id_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Actual finite quotient pullback is injective on rational sheaf cohomology. -/
theorem s4_finite_sheafCohomologyPullback_injective
    {X Y : TopCat.{0}} [T2Space X] {G : Type*}
    [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x))
    (f : C(X, Y)) (hf : IsClosedMap f)
    (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite) (hq : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) (n : ℕ) :
    Function.Injective (s4_finite_sheafCohomologyPullback f hf hfin n) := by
  have h := s4_finite_sheafCohomology_retraction hc f hf hfin hq horb hfg n
  have hl : Function.LeftInverse
      (s4_finite_sheafCohomologyTransfer hc f hf hfin hq horb hfg n)
      (s4_finite_sheafCohomologyPullback f hf hfin n) := by
    intro z
    exact DFunLike.congr_fun h z
  exact hl.injective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The finite-map comparison transports the exact invariant image into source cohomology. -/
theorem s4_finite_sheafCohomologyPullback_range
    {X Y : TopCat.{0}} [T2Space X] {G : Type*}
    [Group G] [Fintype G] [MulAction G X]
    (hc : ∀ g : G, Continuous (fun x : X => g • x))
    (f : C(X, Y)) (hf : IsClosedMap f)
    (hfin : ∀ y : Y, (f ⁻¹' {y}).Finite) (hq : Topology.IsQuotientMap f)
    (horb : ∀ x y : X, f x = f y → ∃ g : G, g • x = y)
    (hfg : ∀ (g : G) (x : X), f (g • x) = f x) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} (s4_locallyConstantSheaf X) n) :
    let e := s4_finite_closed_sheafCohomologyEquiv (TopCat.ofHom f) hf hfin
      (s4_locallyConstantSheaf X) n
    (∃ b, s4_finite_sheafCohomologyPullback f hf hfin n b = a) ↔
      ∀ g : G, CategoryTheory.Sheaf.H.map (s4_quotient_deckSheaf hc f hfg g) n
        (e.symm a) = e.symm a := by
  let e := s4_finite_closed_sheafCohomologyEquiv (TopCat.ofHom f) hf hfin
    (s4_locallyConstantSheaf X) n
  let E := (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift ℤ))
  have h := s4_quotient_ext_invariant_range hc f hq horb hfg E n (e.symm a)
  constructor
  · rintro ⟨b, hb⟩
    apply h.mp
    refine ⟨b, ?_⟩
    apply e.injective
    change s4_finite_sheafCohomologyPullback f hf hfin n b = e (e.symm a)
    rw [e.apply_symm_apply]
    exact hb
  · intro ha
    obtain ⟨b, hb⟩ := h.mpr ha
    refine ⟨b, ?_⟩
    change e ((Abelian.extFunctorObj E n).map (s4_quotient_pullbackSheaf f) b) = a
    rw [hb, e.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual rational coefficient identification induces the cohomology equivalence. -/
def s4_rationalSectionCohomologyEquiv
    (T : Over (AlgebraicGeometry.Spec (CommRingCat.of ℂ))) (n : ℕ) :
    HodgeLean.RealDefs.HQ T n ≃+
      CategoryTheory.Sheaf.H.{0}
        (s4_locallyConstantSheaf (TopCat.of (AlgebraicGeometry.ComplexPoint T))) n := by
  exact ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology (TopCat.of (AlgebraicGeometry.ComplexPoint T))) n).mapIso
      (s4_constantSheaf_locallyConstantIso
        (TopCat.of (AlgebraicGeometry.ComplexPoint T)))).addCommGroupIsoToAddEquiv

open AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Finite projective pullback in the repository's rational sheaf-cohomology carrier. -/
def s4_finite_rationalSheafPullback
    {T W : Over (Spec ↧ℂ)} [IsProjective T.hom] [IsProjective W.hom]
    (q : T ⟶ W) [IsFinite q.left] (n : ℕ) : HQ W n →ₗ[ℚ] HQ T n := by
  letI : T2Space (ComplexPoint T) := HodgeLean.Foundations.Analytic.f4_t2Space T
  letI : T2Space (ComplexPoint W) := HodgeLean.Foundations.Analytic.f4_t2Space W
  let eT := s4_rationalSectionCohomologyEquiv T n
  let eW := s4_rationalSectionCohomologyEquiv W n
  let p := s4_finite_sheafCohomologyPullback
    (X := TopCat.of (ComplexPoint T)) (Y := TopCat.of (ComplexPoint W))
    (Point.continuousMap q)
    (Point.continuousMap q).continuous.isClosedMap (s4_finite_complex_fibres q) n
  exact (eT.symm.toAddMonoidHom.comp (p.comp eW.toAddMonoidHom)).toRatLinearMap

end HodgeLean.Foundations.Program
