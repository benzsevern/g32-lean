import HodgeLean.Foundations.Program.SchoenCycleSliceHelpers
import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedOpenPairCharts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual retained blowup has an open chart over every open base chart
where the centre is the unit ideal, with precisely the full inverse-image range.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13. -/
theorem s2v_i2a_unit_centre_open_chart
    {B B' U : Over (Spec ↧ℂ)} (b : B' ⟶ B) (I : B.left.IdealSheafData)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ V : T.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap f.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! v : T ⟶ B', v ≫ b = f)
    (j : U ⟶ B) [IsOpenImmersion j.left] (hI : I.comap j.left = ⊤) :
    ∃ s : U ⟶ B', s ≫ b = j ∧ IsOpenImmersion s.left ∧
      Set.range s.left = b.left ⁻¹' Set.range j.left := by
  letI : IsIso (pullback.snd b j) := s2e_blowup_isIso_off_centre b I huniv j hI
  have hpb := (IsPullback.of_hasPullback b j).map (Over.forget (Spec ↧ℂ))
  haveI : IsOpenImmersion (pullback.fst b j).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip
      (show IsOpenImmersion j.left from inferInstance)
  let s : U ⟶ B' := inv (pullback.snd b j) ≫ pullback.fst b j
  have hs : s ≫ b = j := by
    dsimp [s]
    rw [Category.assoc, pullback.condition, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  haveI : IsOpenImmersion s.left :=
    inferInstanceAs (IsOpenImmersion ((inv (pullback.snd b j)).left ≫ (pullback.fst b j).left))
  refine ⟨s, hs, inferInstance, ?_⟩
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨q, ?_⟩
    exact (congrArg (fun f : U ⟶ B => f.left q) hs).symm
  · rintro ⟨q, hq⟩
    obtain ⟨z, hzp, _⟩ := Scheme.exists_preimage_of_isPullback hpb p q hq.symm
    refine ⟨(pullback.snd b j).left z, ?_⟩
    have hsec : pullback.snd b j ≫ s = pullback.fst b j := by
      dsimp [s]
      rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    exact (congrArg (fun f => f.left z) hsec).trans hzp

end HodgeLean.Foundations.Program
