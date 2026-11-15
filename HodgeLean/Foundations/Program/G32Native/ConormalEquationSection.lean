import HodgeLean.Foundations.BundleThom.ImmersionDefs
import HodgeLean.Foundations.Program.G32Native.CanonicalConormalEvaluation
import HodgeLean.Foundations.Program.G32Native.ModuleSectionValueFactorization
import HodgeLean.Foundations.Program.G32Native.PullbackAssociativity
import HodgeLean.Foundations.Program.G32Native.ConormalPointFibreTransport

/-! # Actual equation sections on the source of an immersion -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native

/-- Inverting the intermediate comparison retains the direct point pullback. -/
theorem pullbackComp_inverse_associativity {A B C D : Scheme.{0}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (M : D.Modules) :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).inv.app M) ≫
      (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj M) ≫
      (Scheme.Modules.pullbackComp (a ≫ b) c).hom.app M =
      (Scheme.Modules.pullbackComp a (b ≫ c)).hom.app M := by
  let F := Scheme.Modules.pullback a
  let e := Scheme.Modules.pullbackComp b c
  let z := (Scheme.Modules.pullbackComp a (b ≫ c)).hom.app M
  have h := pullbackComp_associativity_hom a b c M
  have hi : F.map (e.inv.app M) ≫ F.map (e.hom.app M) = 𝟙 _ :=
    (F.map_comp _ _).symm.trans (by rw [e.inv_hom_id_app, F.map_id])
  calc
    _ = F.map (e.inv.app M) ≫
        ((Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj M) ≫
          (Scheme.Modules.pullbackComp (a ≫ b) c).hom.app M) := Category.assoc _ _ _
    _ = F.map (e.inv.app M) ≫ (F.map (e.hom.app M) ≫ z) :=
      congrArg (fun t => F.map (e.inv.app M) ≫ t) h.symm
    _ = (F.map (e.inv.app M) ≫ F.map (e.hom.app M)) ≫ z := (Category.assoc _ _ _).symm
    _ = z := (congrArg (fun t => t ≫ z) hi).trans (Category.id_comp z)

#print axioms pullbackComp_inverse_associativity

/-- Evaluation of an iterated pullback section retains its original point
factorization after the intermediate composition comparison is inverted. -/
theorem pullbackPointSection_iterated {A B C D : Scheme.{0}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (p : A ⟶ C) (q : A ⟶ D)
    (hp : a ≫ b = p) (hq : p ≫ c = q) (M : D.Modules)
    (t : unit B ⟶ (Scheme.Modules.pullback (b ≫ c)).obj M) :
    (pullbackUnit a).inv ≫
        (Scheme.Modules.pullback a).map (t ≫ (Scheme.Modules.pullbackComp b c).inv.app M) ≫
      (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj M) ≫
      (Scheme.Modules.pullbackCongr hp).hom.app ((Scheme.Modules.pullback c).obj M) ≫
      (Scheme.Modules.pullbackComp p c).hom.app M ≫
      (Scheme.Modules.pullbackCongr hq).hom.app M =
    (pullbackUnit a).inv ≫ (Scheme.Modules.pullback a).map t ≫
      (Scheme.Modules.pullbackComp a (b ≫ c)).hom.app M ≫
      (Scheme.Modules.pullbackCongr (by rw [← Category.assoc, hp, hq])).hom.app M := by
  cases hp
  cases hq
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id, Category.id_comp, Functor.map_comp, Category.assoc]
  exact congrArg (fun z => (pullbackUnit a).inv ≫ (Scheme.Modules.pullback a).map t ≫ z)
    (pullbackComp_inverse_associativity a b c M)

#print axioms pullbackPointSection_iterated


/-- Pull an actual ambient ideal equation to its actual conormal section on
the inverse image of its domain.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8, pullback of ideal sections. -/
def conormalEquationSection {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W) (U : W.left.Opens)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)) :
    unit (i.left ⁻¹ᵁ U).toScheme ⟶
      (Scheme.Modules.pullback (i.left ⁻¹ᵁ U).ι).obj (Conormal.sheaf i.left) :=
  (i1_moduleSectionPullback (i.left ∣_ U)
      ((Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)) s ≫
    (Scheme.Modules.pullbackComp (i.left ∣_ U) U.ι).hom.app _ ≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι i.left U)).hom.app _) ≫
    (Scheme.Modules.pullbackComp (i.left ⁻¹ᵁ U).ι i.left).inv.app _

#print axioms conormalEquationSection


/-- A specified point factorization gives the same local section morphism. -/
theorem modulePointSection_factorization {W : Over (Spec ↧ℂ)} (M : W.left.Modules)
    (U : W.left.Opens) (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (p : ComplexPoint W) (hp : p ∈ Point.overOpen U)
    (q : Spec ↧ℂ ⟶ U.toScheme) (hq : q ≫ U.ι = p.left) :
    (pullbackUnit q).inv ≫ (Scheme.Modules.pullback q).map s ≫
      (Scheme.Modules.pullbackComp q U.ι).hom.app M ≫
      (Scheme.Modules.pullbackCongr hq).hom.app M =
    i1_localModuleSectionSpecialization M U s p hp := by
  have ha : q = liftToOpen W U p hp :=
    (cancel_mono U.ι).mp (hq.trans (liftToOpen_fac W U p hp).symm)
  subst q
  rfl

#print axioms modulePointSection_factorization
/-- The original equation sections retain the actual point pullback comparison. -/
theorem conormalEquationSection_point_comparison {Q W : Over (Spec ↧ℂ)}
    (i : Q ⟶ W) (U : W.left.Opens)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left))
    (x : ComplexPoint Q) (hx : Point.map i x ∈ Point.overOpen U) :
    i1_localModuleSectionSpecialization (Conormal.sheaf i.left) (i.left ⁻¹ᵁ U)
        (conormalEquationSection i U s) x ((Point.mem_overOpen_map_iff i x U).mp hx) ≫
      (Scheme.Modules.pullbackComp x.left i.left).hom.app (Conormal.idealModule i.left) =
    i1_localModuleSectionSpecialization (Conormal.idealModule i.left) U s (Point.map i x) hx := by
  let M := Conormal.idealModule i.left
  let V := i.left ⁻¹ᵁ U
  have hxV : x ∈ Point.overOpen V := (Point.mem_overOpen_map_iff i x U).mp hx
  let a := liftToOpen Q V x hxV
  let g := i.left ∣_ U
  have ha : a ≫ V.ι = x.left := liftToOpen_fac Q V x hxV
  have hg : g ≫ U.ι = V.ι ≫ i.left := morphismRestrict_ι i.left U
  have hap : (a ≫ g) ≫ U.ι = (Point.map i x).left := by
    calc
      _ = a ≫ (g ≫ U.ι) := Category.assoc _ _ _
      _ = a ≫ (V.ι ≫ i.left) := congrArg (fun t => a ≫ t) hg
      _ = (a ≫ V.ι) ≫ i.left := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun t => t ≫ i.left) ha
  have haq : a ≫ (V.ι ≫ i.left) = (Point.map i x).left :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ i.left) ha)
  let t := i1_moduleSectionPullback g ((Scheme.Modules.pullback U.ι).obj M) s ≫
    (Scheme.Modules.pullbackComp g U.ι).hom.app M ≫
    (Scheme.Modules.pullbackCongr hg).hom.app M
  let L := (pullbackUnit a).inv ≫
    (Scheme.Modules.pullback a).map (conormalEquationSection i U s) ≫
    (Scheme.Modules.pullbackComp a V.ι).hom.app (Conormal.sheaf i.left) ≫
    (Scheme.Modules.pullbackCongr ha).hom.app (Conormal.sheaf i.left)
  let R := (pullbackUnit (a ≫ g)).inv ≫ (Scheme.Modules.pullback (a ≫ g)).map s ≫
    (Scheme.Modules.pullbackComp (a ≫ g) U.ι).hom.app M ≫
    (Scheme.Modules.pullbackCongr hap).hom.app M
  have ht : conormalEquationSection i U s =
      t ≫ (Scheme.Modules.pullbackComp V.ι i.left).inv.app M := rfl
  have h₁ := pullbackPointSection_iterated a V.ι i.left x.left
    (Point.map i x).left ha rfl M t
  have h₂ := i1_moduleSectionTransport_factorization a g U.ι (V.ι ≫ i.left)
    (a ≫ g) (Point.map i x).left hg rfl haq hap M s
  have hLR : L ≫ (Scheme.Modules.pullbackComp x.left i.left).hom.app M = R := by
    apply (show L ≫ (Scheme.Modules.pullbackComp x.left i.left).hom.app M =
      (pullbackUnit a).inv ≫ (Scheme.Modules.pullback a).map t ≫
        (Scheme.Modules.pullbackComp a (V.ι ≫ i.left)).hom.app M ≫
        (Scheme.Modules.pullbackCongr haq).hom.app M from ?_).trans
    · exact h₂
    · simpa only [L, ht, Conormal.sheaf, s2c_conormal, M, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
        NatTrans.id_app, Category.comp_id, Category.assoc] using h₁
  change L ≫ (Scheme.Modules.pullbackComp x.left i.left).hom.app M = _
  exact hLR.trans (modulePointSection_factorization M U s (Point.map i x) hx (a ≫ g) hap)

#print axioms conormalEquationSection_point_comparison

end HodgeLean.Foundations.Program.G32Native
