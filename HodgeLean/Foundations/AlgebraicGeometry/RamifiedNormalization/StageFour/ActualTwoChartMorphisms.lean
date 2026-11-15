import Mathlib.AlgebraicGeometry.Gluing

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Compatible maps on two covering open immersions glue uniquely on the specified actual scheme. -/
theorem glue_two_actual_open_charts
    (X U V Y : Scheme.{0}) (jU : U ⟶ X) (jV : V ⟶ X)
    [IsOpenImmersion jU] [IsOpenImmersion jV]
    (hcover : ∀ x : X, (∃ u, jU u = x) ∨ ∃ v, jV v = x)
    (fU : U ⟶ Y) (fV : V ⟶ Y)
    (hUV : pullback.fst jU jV ≫ fU = pullback.snd jU jV ≫ fV) :
    ∃! f : X ⟶ Y, jU ≫ f = fU ∧ jV ≫ f = fV := by
  let obj : Bool → Scheme := fun b => if b then U else V
  let map : ∀ b, obj b ⟶ X := fun b => by cases b; exact jV; exact jU
  have hc : ∀ x : X, ∃ b y, map b y = x := by
    intro x
    rcases hcover x with ⟨u, hu⟩ | ⟨v, hv⟩
    · exact ⟨true, u, hu⟩
    · exact ⟨false, v, hv⟩
  let C : X.OpenCover := Scheme.Cover.mkOfCovers Bool obj map hc (by
    intro b
    cases b <;> dsimp [map, obj] <;> infer_instance)
  let f : ∀ b, obj b ⟶ Y := fun b => by cases b; exact fV; exact fU
  have hVU : pullback.fst jV jU ≫ fV = pullback.snd jV jU ≫ fU := by
    have he := congrArg (fun q => (pullbackSymmetry jV jU).hom ≫ q) hUV
    simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst,
      pullbackSymmetry_hom_comp_snd] at he
    exact he.symm
  have hf : ∀ a b, pullback.fst (C.f a) (C.f b) ≫ f a = pullback.snd _ _ ≫ f b := by
    intro a b
    cases a <;> cases b
    · change pullback.fst jV jV ≫ fV = pullback.snd jV jV ≫ fV
      have he : pullback.fst jV jV = pullback.snd jV jV := (cancel_mono jV).mp pullback.condition
      rw [he]
    · exact hVU
    · exact hUV
    · change pullback.fst jU jU ≫ fU = pullback.snd jU jU ≫ fU
      have he : pullback.fst jU jU = pullback.snd jU jU := (cancel_mono jU).mp pullback.condition
      rw [he]
  refine ⟨C.glueMorphisms f hf, ?_, ?_⟩
  · exact ⟨C.ι_glueMorphisms f hf true, C.ι_glueMorphisms f hf false⟩
  · intro g hg
    apply C.hom_ext
    intro b
    rw [C.ι_glueMorphisms f hf]
    cases b
    · exact hg.2
    · exact hg.1

end AlgebraicGeometry.RamifiedNormalization.StageFour
