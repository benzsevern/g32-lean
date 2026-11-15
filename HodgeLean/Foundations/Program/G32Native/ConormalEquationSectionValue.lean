import HodgeLean.Foundations.Program.G32Native.ConormalEquationSection

/-! # Point values of actual equation sections -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native

/-- The module section value is the value of its actual local specialization morphism. -/
theorem moduleSectionValue_eq_localSpecialization {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules)
    (U : Q.left.Opens)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    moduleSectionValue M U s x hx =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (i1_localModuleSectionSpecialization M U s x hx) (1 : Γ(Spec ↧ℂ, ⊤)) := rfl

#print axioms moduleSectionValue_eq_localSpecialization

/-- A point-section comparison transports its value through the inverse module isomorphism. -/
theorem pointSectionValue_inv_of_comp {M N : (Spec ↧ℂ).Modules} (e : M ≅ N)
    (a : unit (Spec ↧ℂ) ⟶ M) (c : unit (Spec ↧ℂ) ⟶ N)
    (h : a ≫ e.hom = c) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map a (1 : Γ(Spec ↧ℂ, ⊤)) =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map e.inv
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map c (1 : Γ(Spec ↧ℂ, ⊤))) := by
  rw [e.eq_comp_inv.mpr h, Functor.map_comp, ModuleCat.comp_apply]

#print axioms pointSectionValue_inv_of_comp

/-- The original equation section specializes to the original conormal class. -/
theorem moduleSectionValue_conormalEquationSection {Q W : Over (Spec ↧ℂ)}
    (i : Q ⟶ W) (U : W.left.Opens)
    (s : unit U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left))
    (x : ComplexPoint Q) (hx : Point.map i x ∈ Point.overOpen U) :
    moduleSectionValue (Conormal.sheaf i.left) (i.left ⁻¹ᵁ U)
        (conormalEquationSection i U s) x ((Point.mem_overOpen_map_iff i x U).mp hx) =
      conormalLocalClass i U s x hx := by
  unfold conormalLocalClass
  rw [moduleSectionValue_eq_localSpecialization, moduleSectionValue_eq_localSpecialization]
  exact pointSectionValue_inv_of_comp
    ((Scheme.Modules.pullbackComp x.left i.left).app (Conormal.idealModule i.left))
    (i1_localModuleSectionSpecialization (Conormal.sheaf i.left) (i.left ⁻¹ᵁ U)
      (conormalEquationSection i U s) x ((Point.mem_overOpen_map_iff i x U).mp hx))
    (i1_localModuleSectionSpecialization (Conormal.idealModule i.left) U s (Point.map i x) hx)
    (conormalEquationSection_point_comparison i U s x hx)

#print axioms moduleSectionValue_conormalEquationSection

end HodgeLean.Foundations.Program.G32Native
