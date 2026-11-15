import HodgeLean.Foundations.AbelianQuotient.Defs

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

set_option maxRecDepth 2000 in
/-- A subobject stable under the group operations inherits a group object structure. -/
theorem group_subobject {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {H G : C} [GrpObj G] (i : H ⟶ G) [Mono i]
    (e : 𝟙_ C ⟶ H) (m : H ⊗ H ⟶ H) (v : H ⟶ H)
    (he : e ≫ i = η[G]) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[G])
    (hv : v ≫ i = i ≫ ι[G]) :
    ∃ gh : GrpObj H, letI := gh; IsMonHom i := by
  let S (T : C) : Subgroup (T ⟶ G) :=
    { carrier := Set.range (fun f : T ⟶ H => f ≫ i)
      one_mem' := ⟨toUnit T ≫ e, by
        change (toUnit T ≫ e) ≫ i = 1
        rw [Category.assoc, he]; rfl⟩
      mul_mem' := by
        rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
        refine ⟨lift f g ≫ m, ?_⟩
        change (lift f g ≫ m) ≫ i = (f ≫ i) * (g ≫ i)
        rw [Category.assoc, hm, ← Category.assoc, lift_map]
        rfl
      inv_mem' := by
        rintro _ ⟨f, rfl⟩
        refine ⟨f ≫ v, ?_⟩
        change (f ≫ v) ≫ i = (f ≫ i)⁻¹
        rw [Category.assoc, hv, ← Category.assoc]
        rfl }
  let F : Cᵒᵖ ⥤ GrpCat :=
    { obj T := GrpCat.of (S T.unop)
      map {T U} f := GrpCat.ofHom
        { toFun := fun a => ⟨f.unop ≫ a.val, by
            obtain ⟨g, hg⟩ := a.property
            change g ≫ i = a.val at hg
            exact ⟨f.unop ≫ g, by
              change (f.unop ≫ g) ≫ i = f.unop ≫ a.val
              rw [Category.assoc, hg]⟩⟩
          map_one' := Subtype.ext (MonObj.comp_one f.unop)
          map_mul' := fun a b => Subtype.ext (MonObj.comp_mul f.unop a.val b.val) }
      map_id T := by
        apply GrpCat.hom_ext
        apply MonoidHom.ext
        intro a
        apply Subtype.ext
        exact Category.id_comp a.val
      map_comp f g := by
        apply GrpCat.hom_ext
        apply MonoidHom.ext
        intro a
        apply Subtype.ext
        exact Category.assoc _ _ _ }
  let α : (F ⋙ forget GrpCat).RepresentableBy H :=
    { homEquiv :=
        { toFun := fun f => ⟨f ≫ i, ⟨f, rfl⟩⟩
          invFun := fun a => Classical.choose a.property
          left_inv := fun f => (cancel_mono i).mp (Classical.choose_spec
            (show f ≫ i ∈ S _ from ⟨f, rfl⟩))
          right_inv := fun a => Subtype.ext (Classical.choose_spec a.property) }
      homEquiv_comp f g := Subtype.ext (Category.assoc _ _ _) }
  let gh := GrpObj.ofRepresentableBy H F α
  letI := gh
  let β : F ⟶ yonedaGrpObj G :=
    { app T := GrpCat.ofHom (S T.unop).subtype
      naturality {T U} f := by
        apply GrpCat.hom_ext
        apply MonoidHom.ext
        intro a
        rfl }
  let E := yonedaGrpObjIsoOfRepresentableBy H F α
  let j : Grp.mk H ⟶ Grp.mk G := yonedaGrpFullyFaithful.preimage (X := Grp.mk H) (Y := Grp.mk G) (E.hom ≫ β)
  have hj : j.hom.hom = i := by
    have h := yonedaGrpFullyFaithful.map_preimage (X := Grp.mk H) (Y := Grp.mk G) (E.hom ≫ β)
    have hh := congrArg (fun t => (t.app (Opposite.op H)) (𝟙 H)) h
    change 𝟙 H ≫ j.hom.hom = 𝟙 H ≫ i at hh
    simpa only [Category.id_comp] using hh
  refine ⟨gh, ?_⟩
  rw [← hj]
  infer_instance

/-- Preservation of the monoid operations can be checked after a monic monoid morphism. -/
theorem isMonHom_of_mono_comp {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {M H G : C} [MonObj M] [MonObj H] [MonObj G]
    (f : M ⟶ H) (i : H ⟶ G) [Mono i] [IsMonHom i] [IsMonHom (f ≫ i)] :
    IsMonHom f := by
  refine ⟨?_, ?_⟩
  · apply (cancel_mono i).mp
    rw [Category.assoc, IsMonHom.one_hom (f ≫ i), IsMonHom.one_hom i]
  · apply (cancel_mono i).mp
    calc
      (μ[M] ≫ f) ≫ i = μ[M] ≫ (f ≫ i) := Category.assoc _ _ _
      _ = ((f ≫ i) ⊗ₘ (f ≫ i)) ≫ μ[G] := IsMonHom.mul_hom _
      _ = (f ⊗ₘ f) ≫ (i ⊗ₘ i) ≫ μ[G] := by rw [← tensorHom_comp_tensorHom, Category.assoc]
      _ = ((f ⊗ₘ f) ≫ μ[H]) ≫ i := by
        rw [Category.assoc, IsMonHom.mul_hom i]

end HodgeLean.Foundations.AbelianQuotient
