import HodgeLean.Foundations.BundleThom.ModuleSectionPullbackHelpers

/-! # Compatibility of section transport through successive scheme morphisms

Every comparison is the canonical pullback comparison of the actual morphisms.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- Canonical pullback comparisons satisfy the componentwise associativity identity.
Source: Hartshorne, Algebraic Geometry, II.5, associativity of module-sheaf pullback. -/
theorem i1_pullbackComparison_associativity {A B C D : Scheme.{0}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (M : D.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M =
      (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M := by
  let e₁ := Scheme.Modules.pullbackComp f (g ≫ h)
  let e₂ := Functor.isoWhiskerRight (Scheme.Modules.pullbackComp g h) (Scheme.Modules.pullback f)
  let e₃ := Functor.isoWhiskerLeft (Scheme.Modules.pullback h) (Scheme.Modules.pullbackComp f g)
  let e₄ := Scheme.Modules.pullbackComp (f ≫ g) h
  have ha : e₃.hom ≫ e₄.hom =
      (Functor.associator _ _ _).inv ≫ e₂.hom ≫ e₁.hom :=
    congr($(SheafOfModules.pullback_assoc.{0}
      h.toRingCatSheafHom g.toRingCatSheafHom f.toRingCatSheafHom).hom)
  have hc := congrArg (fun z => z.app M) ha
  change (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M =
    𝟙 _ ≫ ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M) at hc
  exact (hc.trans (Category.id_comp _)).symm

/-- Transport through an intermediate scheme agrees with direct transport of the actual section.
Source: Hartshorne, Algebraic Geometry, II.5, composition of pullbacks of local sections. -/
theorem i1_moduleSectionTransport_composition {A B C D : Scheme.{0}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (M : D.Modules)
    (s : SheafOfModules.unit.{0} C.ringCatSheaf ⟶ (Scheme.Modules.pullback h).obj M) :
    i1_moduleSectionPullback f ((Scheme.Modules.pullback (g ≫ h)).obj M)
        (i1_moduleSectionPullback g ((Scheme.Modules.pullback h).obj M) s ≫
          (Scheme.Modules.pullbackComp g h).hom.app M) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M =
      i1_moduleSectionPullback (f ≫ g) ((Scheme.Modules.pullback h).obj M) s ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M := by
  let F := Scheme.Modules.pullback f
  let N := (Scheme.Modules.pullback h).obj M
  let t := i1_moduleSectionPullback g N s
  let a := (Scheme.Modules.pullbackComp g h).hom.app M
  let b := (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M
  let c := (Scheme.Modules.pullbackComp f g).hom.app N
  let d := (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M
  let u := i1_moduleSectionPullback f ((Scheme.Modules.pullback g).obj N) t
  have hn : i1_moduleSectionPullback f ((Scheme.Modules.pullback (g ≫ h)).obj M) (t ≫ a) =
      u ≫ F.map a := i1_moduleSectionPullback_naturality f a t
  have ha : F.map a ≫ b = c ≫ d := i1_pullbackComparison_associativity f g h M
  have hs : u ≫ c = i1_moduleSectionPullback (f ≫ g) N s :=
    i1_moduleSectionPullback_composition f g N s
  calc
    _ = (u ≫ F.map a) ≫ b := congrArg (fun z => z ≫ b) hn
    _ = u ≫ (F.map a ≫ b) := Category.assoc _ _ _
    _ = u ≫ (c ≫ d) := congrArg (fun z => u ≫ z) ha
    _ = (u ≫ c) ≫ d := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun z => z ≫ d) hs

/-- Section transport is independent of the specified factorization through the intermediate scheme.
Source: Hartshorne, Algebraic Geometry, II.5, functoriality of section restriction and fibres. -/
theorem i1_moduleSectionTransport_factorization {A B C D : Scheme.{0}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (k : B ⟶ D) (p : A ⟶ C) (m : A ⟶ D)
    (hk : g ≫ h = k) (hp : f ≫ g = p) (hc : f ≫ k = m) (hd : p ≫ h = m)
    (M : D.Modules)
    (s : SheafOfModules.unit.{0} C.ringCatSheaf ⟶ (Scheme.Modules.pullback h).obj M) :
    i1_moduleSectionPullback f ((Scheme.Modules.pullback k).obj M)
        (i1_moduleSectionPullback g ((Scheme.Modules.pullback h).obj M) s ≫
          (Scheme.Modules.pullbackComp g h).hom.app M ≫
            (Scheme.Modules.pullbackCongr hk).hom.app M) ≫
      (Scheme.Modules.pullbackComp f k).hom.app M ≫
        (Scheme.Modules.pullbackCongr hc).hom.app M =
      i1_moduleSectionPullback p ((Scheme.Modules.pullback h).obj M) s ≫
        (Scheme.Modules.pullbackComp p h).hom.app M ≫
          (Scheme.Modules.pullbackCongr hd).hom.app M := by
  subst k
  subst p
  subst m
  have hzero : hd = rfl := Subsingleton.elim _ _
  subst hzero
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id]
  exact i1_moduleSectionTransport_composition f g h M s

end HodgeLean.Foundations.BundleThom
