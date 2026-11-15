import HodgeLean.Foundations.Curves.Picard.LineBundles.AdjunctionComparison

/-! # The actual adjunction for pullback to an open

The comparison with restriction retains the explicit restriction maps on sections.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- The comparison between two left adjoints preserves their adjoint maps. -/
theorem homEquiv_leftAdjointUniq_inv {C D : Type*} [Category C] [Category D]
    {F H : C ⥤ D} {G : D ⥤ C} (A : F ⊣ G) (B : H ⊣ G)
    (M : C) (N : D) (h : F.obj M ⟶ N) :
    B.homEquiv M N (((A.leftAdjointUniq B).app M).inv ≫ h) = A.homEquiv M N h := by
  have hu : A.unit.app M ≫ G.map ((A.leftAdjointUniq B).app M).hom = B.unit.app M := by
    simpa only [Iso.app_hom] using Adjunction.unit_leftAdjointUniq_hom_app A B M
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← hu]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The actual open-restriction comparison preserves the pullback adjunction. -/
theorem restrictPullback_adjunct {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (N : X.Modules) (h : M.restrict f ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N
      (((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv ≫ h) =
      (Scheme.Modules.restrictAdjunction f).homEquiv M N h :=
  homEquiv_leftAdjointUniq_inv (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) M N h

/-- The actual open-restriction adjoint map applies the specified module restriction. -/
theorem restrictAdjunct_section {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (N : X.Modules) (h : M.restrict f ⟶ N) (U : Y.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.restrictAdjunction f).homEquiv M N h).app U s =
      h.app (f ⁻¹ᵁ U) (M.presheaf.map (homOfLE (f.image_preimage_le U)).op s) := rfl

/-- The inverse open restriction comparison preserves the actual adjunction units. -/
theorem restrictPullback_unit_inv {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv =
      (Scheme.Modules.restrictAdjunction f).unit.app M := by
  have h := homEquiv_leftAdjointUniq_inv (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) M (M.restrict f) (𝟙 _)
  simp only [Category.comp_id, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id] at h
  exact h.trans (Category.comp_id _)

end HodgeLean.Foundations.Curves.Picard.LineBundles
