import HodgeLean.Foundations.Program.SchoenTransferQ3SupportOpenDiagram
import HodgeLean.Foundations.Program.SchoenTransferQ3TangentialOpenRestriction
import HodgeLean.Foundations.Program.SchoenTransferQ3TangentialGenericPoint

/-! One actual common tangential-base cut retaining the support generic point. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The common dense tangential-base cut retains the actual generic support,
full finite ambient inverse image, closed support squares and smooth maps. -/
theorem s4_q3_retained_tangential_base_cut
    {C D X W T : Over (Spec ↧ℂ)} [IsIntegral C.left] [IsIntegral T.left]
    [Smooth D.hom] [Smooth X.hom] [Smooth W.hom]
    (i : C ⟶ X) (j : D ⟶ W) [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (f : C ⟶ D) [Etale f.left] (q : X ⟶ W) [IsFinite q.left] [Flat q.left]
    (h : W ⟶ T) [Etale (j ≫ h).left] (hsquare : i ≫ q = f ≫ j)
    (A : T.left.Opens) (hdA : Dense (A : Set T.left))
    (hsW : Smooth (h.left ∣_ A)) (hsX : Smooth ((q.left ≫ h.left) ∣_ A)) :
    let S := j.left ⁻¹ᵁ (h.left ⁻¹ᵁ A)
    ∃ V : W.left.Opens, V ≤ h.left ⁻¹ᵁ A ∧ j.left ⁻¹ᵁ V = S ∧
      genericPoint C.left ∈ f.left ⁻¹ᵁ S ∧
      ∃ (i' : openScheme C (f.left ⁻¹ᵁ S) ⟶ openScheme X (q.left ⁻¹ᵁ V))
        (j' : openScheme D S ⟶ openScheme W V)
        (f' : openScheme C (f.left ⁻¹ᵁ S) ⟶ openScheme D S)
        (q' : openScheme X (q.left ⁻¹ᵁ V) ⟶ openScheme W V)
        (H : openScheme W V ⟶ openScheme T A),
        i' ≫ q' = f' ≫ j' ∧
        i' ≫ openInclusion X (q.left ⁻¹ᵁ V) = openInclusion C (f.left ⁻¹ᵁ S) ≫ i ∧
        j' ≫ openInclusion W V = openInclusion D S ≫ j ∧
        openInclusion X (q.left ⁻¹ᵁ V) ≫ q = q' ≫ openInclusion W V ∧
        f'.left = f.left ∣_ S ∧ q'.left = q.left ∣_ V ∧
        IsClosedImmersion i'.left ∧ IsClosedImmersion j'.left ∧
        IsFinite q'.left ∧ Flat q'.left ∧ Etale f'.left ∧
        Smooth H.left ∧ Smooth (q' ≫ H).left ∧
        Etale (j' ≫ H).left ∧ Etale (i' ≫ q' ≫ H).left ∧
        Smooth (openScheme D S).hom ∧ Smooth (openScheme C (f.left ⁻¹ᵁ S)).hom ∧
        IsPullback i'.left (f.left ⁻¹ᵁ S).ι (q.left ⁻¹ᵁ V).ι i.left ∧
        IsPullback j'.left S.ι V.ι j.left ∧
        IsPullback q'.left (q.left ⁻¹ᵁ V).ι V.ι q.left := by
  let S := j.left ⁻¹ᵁ (h.left ⁻¹ᵁ A)
  have hsD : Smooth (S.ι ≫ D.hom) := inferInstance
  have heS : Etale (f.left ∣_ S) := inferInstance
  obtain ⟨V, hVA, hVS, i', j', f', q', hsq, hi, hj, hf, hq,
    hiClosed, hjClosed, hfinite, heF, hsD', hsC', hcartI, hcartJ, _, hcartQ⟩ :=
    s4_q3_support_open_square i j f q hsquare (h.left ⁻¹ᵁ A) S le_rfl hsD heS
  let H : openScheme W V ⟶ openScheme T A := Over.homMk (h.left.resLE A V hVA) (by
    change h.left.resLE A V hVA ≫ A.ι ≫ T.hom = V.ι ≫ W.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w h])
  have hambient : openInclusion X (q.left ⁻¹ᵁ V) ≫ q = q' ≫ openInclusion W V := by
    apply Over.OverMorphism.ext
    change (q.left ⁻¹ᵁ V).ι ≫ q.left = q'.left ≫ V.ι
    rw [hq, morphismRestrict_ι]
  obtain ⟨hsmH, hsmQH⟩ := s4_q3_smooth_tangential_open_restriction q.left h.left A V hVA hsW hsX
  have hsmQH' : Smooth (q' ≫ H).left := by
    change Smooth (q'.left ≫ h.left.resLE A V hVA)
    rw [hq]
    exact hsmQH
  letI : Etale (j.left ≫ h.left) := inferInstanceAs (Etale (j ≫ h).left)
  have hgen : genericPoint C.left ∈ f.left ⁻¹ᵁ S := by
    change (f.left ≫ j.left ≫ h.left) (genericPoint C.left) ∈ A
    exact s4_q3_etale_support_generic_mem_dense_base (f.left ≫ j.left ≫ h.left) A hdA
  have hjraw : j'.left ≫ V.ι = S.ι ≫ j.left := congrArg Over.Hom.left hj
  have hJ : j'.left ≫ H.left =
      (j.left ≫ h.left).resLE A S (fun y hy => hy) := by
    apply (cancel_mono A.ι).mp
    calc
      (j'.left ≫ H.left) ≫ A.ι = j'.left ≫ (V.ι ≫ h.left) := by
        change (j'.left ≫ h.left.resLE A V hVA) ≫ A.ι = _
        rw [Category.assoc, Scheme.Hom.resLE_comp_ι]
      _ = (S.ι ≫ j.left) ≫ h.left := by rw [← Category.assoc, hjraw]
      _ = (j.left ≫ h.left).resLE A S (fun y hy => hy) ≫ A.ι := by
        rw [Scheme.Hom.resLE_comp_ι, Category.assoc]
  have heJ : Etale (j' ≫ H).left := by
    change Etale (j'.left ≫ H.left)
    rw [hJ]
    dsimp only [Scheme.Hom.resLE]
    infer_instance
  letI : Etale (j' ≫ H).left := heJ
  letI : Etale f'.left := heF
  have heI : Etale (i' ≫ q' ≫ H).left := by
    rw [← Category.assoc, hsq, Category.assoc]
    change Etale (f'.left ≫ (j' ≫ H).left)
    infer_instance
  have hflat : Flat q'.left := by rw [hq]; infer_instance
  exact ⟨V, hVA, hVS, hgen, i', j', f', q', H, hsq, hi, hj, hambient,
    hf, hq, hiClosed, hjClosed, hfinite, hflat, heF, hsmH, hsmQH', heJ, heI,
    hsD', hsC', hcartI, hcartJ, hcartQ⟩

end HodgeLean.Foundations.Program
