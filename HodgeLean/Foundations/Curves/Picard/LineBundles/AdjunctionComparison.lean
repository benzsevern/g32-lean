import HodgeLean.Foundations.Curves.Picard.LineBundles.PullbackTensor

/-! # Adjoint comparison of tensor maps

The comparison uses the actual mate of a transformation between left adjoints.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- Passing across a left adjoint comparison is the mate comparison on adjoints. -/
theorem homEquiv_conjugate {C D : Type*} [Category C] [Category D]
    {F₁ F₂ : C ⥤ D} {G₁ G₂ : D ⥤ C} (A : F₁ ⊣ G₁) (B : F₂ ⊣ G₂)
    (a : F₂ ⟶ F₁) {M : C} {N : D} (h : F₁.obj M ⟶ N) :
    B.homEquiv M N (a.app M ≫ h) =
      A.homEquiv M N h ≫ (conjugateEquiv A B a).app N := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, ← unit_conjugateEquiv A B a M]
  simp only [Category.assoc]
  rw [← (conjugateEquiv A B a).naturality h]

/-- The actual pullback composition comparison has the pushforward composition adjoint. -/
theorem pullbackComp_adjunct {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (N : X.Modules)
    (h : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv M N
        (((Scheme.Modules.pullbackComp f g).app M).inv ≫ h) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv M N h ≫
        ((Scheme.Modules.pushforwardComp f g).app N).hom := by
  have he := homEquiv_conjugate
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv h
  simpa only [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Iso.app_hom, Iso.app_inv, Functor.comp_obj] using he

/-- The actual composition comparisons preserve the module adjunction units. -/
theorem pullbackComp_unit {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f)).unit.app M ≫
        ((Scheme.Modules.pushforwardComp f g).app
          ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M))).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
        (Scheme.Modules.pushforward (f ≫ g)).map ((Scheme.Modules.pullbackComp f g).app M).inv := by
  have he := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  simpa only [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Iso.app_hom, Iso.app_inv, Functor.comp_obj] using he

end HodgeLean.Foundations.Curves.Picard.LineBundles
