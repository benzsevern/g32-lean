import HodgeLean.Foundations.Program.CompensationAssemblyGenericSmooth

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

theorem cq_finite_smooth_restrict_inter {X Y : Scheme.{0}} (f : X ⟶ Y) (U V : Y.Opens)
    (hf : IsFinite (f ∣_ U)) (hs : Smooth (f ∣_ V)) :
    IsFinite (f ∣_ (U ⊓ V)) ∧ Smooth (f ∣_ (U ⊓ V)) := by
  letI : MorphismProperty.RespectsIso (@IsFinite.{0}) := by
    apply MorphismProperty.RespectsIso.mk
    · intro S T Z e g hg
      letI : IsFinite g := hg
      infer_instance
    · intro S T Z e g hg
      letI : IsFinite g := hg
      infer_instance
  letI : MorphismProperty.RespectsIso (@Smooth.{0}) := by
    apply MorphismProperty.RespectsIso.mk
    · intro S T Z e g hg
      letI : Smooth g := hg
      infer_instance
    · intro S T Z e g hg
      letI : Smooth g := hg
      infer_instance
  have hfin : IsFinite (f ∣_ U ∣_ (U.ι ⁻¹ᵁ V)) := by
    letI : IsFinite (f ∣_ U) := hf
    infer_instance
  have hsm : Smooth (f ∣_ V ∣_ (V.ι ⁻¹ᵁ U)) := by
    letI : Smooth (f ∣_ V) := hs
    infer_instance
  have hf' := (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).mp hfin
  have hs' := (MorphismProperty.arrow_mk_iso_iff (P := @Smooth)
    (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U))).mp hsm
  have hUV : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = U ⊓ V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hVU : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U ⊓ V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  exact ⟨hUV ▸ hf', hVU ▸ hs'⟩

theorem cq_primeProjection_finite_smooth_neighborhood (A Y : Over (Spec ↧ℂ))
    [CategoryTheory.GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [CategoryTheory.GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5)
    (himage : Order.coheight ((fst A Y).left x) = 3) :
    ∃ U : (a2r_component A ((fst A Y).left x)).left.Opens,
      genericPoint (a2r_component A ((fst A Y).left x)).left ∈ U ∧
      Dense (U : Set (a2r_component A ((fst A Y).left x)).left) ∧
      IsFinite ((cq_primeProjection A Y x).left ∣_ U) ∧
      Smooth ((cq_primeProjection A Y x).left ∣_ U) := by
  obtain ⟨V, hV, -, hf⟩ := cq_primeProjection_finite_neighborhood A Y hA hY x hx himage
  obtain ⟨W, hW, -, hs⟩ := cq_primeProjection_smooth_neighborhood A Y hA hY x hx himage
  have hp := cq_finite_smooth_restrict_inter (cq_primeProjection A Y x).left V W hf hs
  exact ⟨V ⊓ W, ⟨hV, hW⟩, (V ⊓ W).isOpen.dense ⟨_, ⟨hV, hW⟩⟩, hp.1, hp.2⟩

end HodgeLean.Foundations.Program
