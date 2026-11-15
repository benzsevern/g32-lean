import HodgeLean.Foundations.Program.SchoenTransferQ3SupportOpenDiagram
import HodgeLean.Foundations.Program.SchoenTransferQ3TangentialOpenRestriction

/-! Actual ambient refinement of the selected etale support coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- The selected support coordinates extend over one actual common ambient
open, with closed support squares and both smooth tangential restrictions. -/
theorem s4_q3_coordinate_support_ambient_refinement
    {C D X W T : Over (Spec ↧ℂ)}
    (i : C ⟶ X) (j : D ⟶ W) [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (f : C ⟶ D) [Etale f.left] (q : X ⟶ W) [IsFinite q.left] [Flat q.left]
    (hsquare : i ≫ q = f ≫ j)
    (U : W.left.Opens) (V : D.left.Opens) (hVU : V ≤ j.left ⁻¹ᵁ U)
    (h : openScheme W U ⟶ T)
    (hEt : Etale (j.left.resLE U V hVU ≫ h.left))
    (hV : Smooth (V.ι ≫ D.hom)) (A : T.left.Opens)
    (hsW : Smooth (h.left ∣_ A))
    (hsX : Smooth (((q.left ∣_ U) ≫ h.left) ∣_ A)) :
    ∃ B : W.left.Opens, B ≤ U ∧ j.left ⁻¹ᵁ B = V ∧
      ∃ (i' : openScheme C (f.left ⁻¹ᵁ V) ⟶ openScheme X (q.left ⁻¹ᵁ B))
        (j' : openScheme D V ⟶ openScheme W B)
        (f' : openScheme C (f.left ⁻¹ᵁ V) ⟶ openScheme D V)
        (q' : openScheme X (q.left ⁻¹ᵁ B) ⟶ openScheme W B)
        (H : openScheme W B ⟶ T),
        i' ≫ q' = f' ≫ j' ∧
        i' ≫ openInclusion X (q.left ⁻¹ᵁ B) = openInclusion C (f.left ⁻¹ᵁ V) ≫ i ∧
        j' ≫ openInclusion W B = openInclusion D V ≫ j ∧
        openInclusion X (q.left ⁻¹ᵁ B) ≫ q = q' ≫ openInclusion W B ∧
        IsClosedImmersion i'.left ∧ IsClosedImmersion j'.left ∧
        IsFinite q'.left ∧ Flat q'.left ∧ Etale f'.left ∧
        Smooth (H.left ∣_ A) ∧ Smooth ((q'.left ≫ H.left) ∣_ A) ∧
        Etale (j' ≫ H).left ∧ Etale (i' ≫ q' ≫ H).left ∧
        Smooth (openScheme D V).hom ∧ Smooth (openScheme C (f.left ⁻¹ᵁ V)).hom ∧
        IsPullback i'.left (f.left ⁻¹ᵁ V).ι (q.left ⁻¹ᵁ B).ι i.left ∧
        IsPullback j'.left V.ι B.ι j.left ∧
        IsPullback q'.left (q.left ⁻¹ᵁ B).ι B.ι q.left := by
  have heV : Etale (f.left ∣_ V) := inferInstance
  obtain ⟨B, hBU, hBV, i', j', f', q', hsq, hi, hj, hf, hq,
    hiClosed, hjClosed, hfinite, heF, hsD, hsC, hcartI, hcartJ, _, hcartQ⟩ :=
    s4_q3_support_open_square i j f q hsquare U V hVU hV heV
  let aW : openScheme W B ⟶ openScheme W U := Over.homMk (W.left.homOfLE hBU) (by
    change W.left.homOfLE hBU ≫ U.ι ≫ W.hom = B.ι ≫ W.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])
  let H := aW ≫ h
  have hQU : q.left ⁻¹ᵁ B ≤ q.left ⁻¹ᵁ U := fun _ hp => hBU hp
  have hfactor : q'.left ≫ aW.left = X.left.homOfLE hQU ≫ (q.left ∣_ U) := by
    apply (cancel_mono U.ι).mp
    change (q'.left ≫ W.left.homOfLE hBU) ≫ U.ι = _
    rw [Category.assoc, Scheme.homOfLE_ι, hq, morphismRestrict_ι,
      Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have hfactorH : q'.left ≫ H.left = X.left.homOfLE hQU ≫ ((q.left ∣_ U) ≫ h.left) := by
    change q'.left ≫ (aW.left ≫ h.left) = _
    rw [← Category.assoc, hfactor, Category.assoc]
  have hJF : j'.left ≫ aW.left = j.left.resLE U V hVU := by
    apply (cancel_mono U.ι).mp
    change (j'.left ≫ W.left.homOfLE hBU) ≫ U.ι = _
    rw [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι]
    exact congrArg Over.Hom.left hj
  have heJ : Etale (j' ≫ H).left := by
    change Etale (j'.left ≫ (aW.left ≫ h.left))
    rw [← Category.assoc, hJF]
    exact hEt
  letI : Etale (j' ≫ H).left := heJ
  letI : Etale f'.left := heF
  have heI : Etale (i' ≫ q' ≫ H).left := by
    rw [← Category.assoc, hsq, Category.assoc]
    change Etale (f'.left ≫ (j' ≫ H).left)
    infer_instance
  have hsH : Smooth (H.left ∣_ A) := by
    letI := hsW
    change Smooth ((W.left.homOfLE hBU ≫ h.left) ∣_ A)
    rw [morphismRestrict_comp]
    infer_instance
  have hsQH : Smooth ((q'.left ≫ H.left) ∣_ A) := by
    letI := hsX
    rw [hfactorH, morphismRestrict_comp]
    infer_instance
  have hflat : Flat q'.left := by rw [hq]; infer_instance
  have hambient : openInclusion X (q.left ⁻¹ᵁ B) ≫ q = q' ≫ openInclusion W B := by
    apply Over.OverMorphism.ext
    change (q.left ⁻¹ᵁ B).ι ≫ q.left = q'.left ≫ B.ι
    rw [hq, morphismRestrict_ι]
  exact ⟨B, hBU, hBV, i', j', f', q', H, hsq, hi, hj, hambient,
    hiClosed, hjClosed, hfinite, hflat, heF, hsH, hsQH, heJ, heI, hsD, hsC,
    hcartI, hcartJ, hcartQ⟩

end HodgeLean.Foundations.Program
