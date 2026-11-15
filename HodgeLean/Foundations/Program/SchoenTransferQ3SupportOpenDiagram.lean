import HodgeLean.Foundations.Program.SchoenTransferQ3SupportOpenLift
import HodgeLean.Foundations.Program.SchoenTransferQ3SmoothComponentMap

/-! Actual closed support embeddings after a common ambient open restriction. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Exact inverse-image source restriction retains a closed support embedding. -/
theorem s4_q3_closed_support_resLE
    {C X : Scheme} (i : C ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) (V : C.Opens) (heq : V = i ⁻¹ᵁ U) :
    IsClosedImmersion (i.resLE U V (heq.le)) := by
  subst V
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- Exact source restriction supplies the actual cartesian closed-support square. -/
theorem s4_q3_support_resLE_isPullback
    {C X : Scheme} (i : C ⟶ X) (U : X.Opens) (V : C.Opens) (heq : V = i ⁻¹ᵁ U) :
    CategoryTheory.IsPullback (i.resLE U V heq.le) V.ι U.ι i := by
  subst V
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact isPullback_morphismRestrict i U

/-- The actual support square restricts to smooth closed support pieces
inside one common ambient target open and its full inverse image. -/
theorem s4_q3_support_open_square
    {C D X W : Over (Spec ↧ℂ)}
    (i : C ⟶ X) (j : D ⟶ W) [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (f : C ⟶ D) (q : X ⟶ W) [IsFinite q.left]
    (hsquare : i ≫ q = f ≫ j)
    (A : W.left.Opens) (S : D.left.Opens) (hSA : S ≤ j.left ⁻¹ᵁ A)
    (hS : Smooth (S.ι ≫ D.hom)) (hEt : Etale (f.left ∣_ S)) :
    ∃ V : W.left.Opens, V ≤ A ∧ j.left ⁻¹ᵁ V = S ∧
      ∃ (i' : ComplexPoint.openScheme C (f.left ⁻¹ᵁ S) ⟶
            ComplexPoint.openScheme X (q.left ⁻¹ᵁ V))
        (j' : ComplexPoint.openScheme D S ⟶ ComplexPoint.openScheme W V)
        (f' : ComplexPoint.openScheme C (f.left ⁻¹ᵁ S) ⟶ ComplexPoint.openScheme D S)
        (q' : ComplexPoint.openScheme X (q.left ⁻¹ᵁ V) ⟶ ComplexPoint.openScheme W V),
        i' ≫ q' = f' ≫ j' ∧
        i' ≫ ComplexPoint.openInclusion X (q.left ⁻¹ᵁ V) =
          ComplexPoint.openInclusion C (f.left ⁻¹ᵁ S) ≫ i ∧
        j' ≫ ComplexPoint.openInclusion W V = ComplexPoint.openInclusion D S ≫ j ∧
        f'.left = f.left ∣_ S ∧ q'.left = q.left ∣_ V ∧
        IsClosedImmersion i'.left ∧ IsClosedImmersion j'.left ∧
        IsFinite q'.left ∧ Etale f'.left ∧
        Smooth (ComplexPoint.openScheme D S).hom ∧
        Smooth (ComplexPoint.openScheme C (f.left ⁻¹ᵁ S)).hom ∧
        CategoryTheory.IsPullback i'.left (f.left ⁻¹ᵁ S).ι (q.left ⁻¹ᵁ V).ι i.left ∧
        CategoryTheory.IsPullback j'.left S.ι V.ι j.left ∧
        CategoryTheory.IsPullback f'.left (f.left ⁻¹ᵁ S).ι S.ι f.left ∧
        CategoryTheory.IsPullback q'.left (q.left ⁻¹ᵁ V).ι V.ι q.left := by
  obtain ⟨V, hVA, hVS⟩ := s4_q3_support_open_ambient_refinement j.left A S hSA
  have hleft : i.left ≫ q.left = f.left ≫ j.left := congrArg Over.Hom.left hsquare
  have hsource : i.left ⁻¹ᵁ (q.left ⁻¹ᵁ V) = f.left ⁻¹ᵁ S := by
    rw [← Scheme.Hom.comp_preimage, hleft, Scheme.Hom.comp_preimage, hVS]
  let Ci := f.left ⁻¹ᵁ S
  let Xi := q.left ⁻¹ᵁ V
  have hCi : Ci ≤ i.left ⁻¹ᵁ Xi := hsource.symm.le
  have hDi : S ≤ j.left ⁻¹ᵁ V := hVS.symm.le
  let i' : ComplexPoint.openScheme C Ci ⟶ ComplexPoint.openScheme X Xi :=
    Over.homMk (i.left.resLE Xi Ci hCi) (by
      change i.left.resLE Xi Ci hCi ≫ Xi.ι ≫ X.hom = Ci.ι ≫ C.hom
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w i])
  let j' : ComplexPoint.openScheme D S ⟶ ComplexPoint.openScheme W V :=
    Over.homMk (j.left.resLE V S hDi) (by
      change j.left.resLE V S hDi ≫ V.ι ≫ W.hom = S.ι ≫ D.hom
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w j])
  let f' : ComplexPoint.openScheme C Ci ⟶ ComplexPoint.openScheme D S :=
    Over.homMk (f.left ∣_ S) (by
      change (f.left ∣_ S) ≫ S.ι ≫ D.hom = Ci.ι ≫ C.hom
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w f])
  let q' : ComplexPoint.openScheme X Xi ⟶ ComplexPoint.openScheme W V :=
    Over.homMk (q.left ∣_ V) (by
      change (q.left ∣_ V) ≫ V.ι ≫ W.hom = Xi.ι ≫ X.hom
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w q])
  have hclosedI : IsClosedImmersion i'.left :=
    s4_q3_closed_support_resLE i.left Xi Ci hsource.symm
  have hclosedJ : IsClosedImmersion j'.left :=
    s4_q3_closed_support_resLE j.left V S hVS.symm
  have hsq : i' ≫ q' = f' ≫ j' := by
    apply Over.OverMorphism.ext
    apply (cancel_mono V.ι).mp
    change i.left.resLE Xi Ci hCi ≫ (q.left ∣_ V) ≫ V.ι =
      (f.left ∣_ S) ≫ j.left.resLE V S hDi ≫ V.ι
    rw [morphismRestrict_ι, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, hleft]
    simp only [morphismRestrict_ι_assoc, Category.assoc]
    rfl
  have hi : i' ≫ ComplexPoint.openInclusion X Xi = ComplexPoint.openInclusion C Ci ≫ i := by
    apply Over.OverMorphism.ext
    exact Scheme.Hom.resLE_comp_ι i.left hCi
  have hj : j' ≫ ComplexPoint.openInclusion W V = ComplexPoint.openInclusion D S ≫ j := by
    apply Over.OverMorphism.ext
    exact Scheme.Hom.resLE_comp_ι j.left hDi
  have hsD : Smooth (ComplexPoint.openScheme D S).hom := hS
  letI : Etale f'.left := hEt
  letI := hsD
  have hsC : Smooth (ComplexPoint.openScheme C Ci).hom := by
    rw [← Over.w f']
    infer_instance
  exact ⟨V, hVA, hVS, i', j', f', q', hsq, hi, hj, rfl, rfl,
    hclosedI, hclosedJ, inferInstanceAs (IsFinite (q.left ∣_ V)), hEt, hsD, hsC,
    s4_q3_support_resLE_isPullback i.left Xi Ci hsource.symm,
    s4_q3_support_resLE_isPullback j.left V S hVS.symm,
    isPullback_morphismRestrict f.left S, isPullback_morphismRestrict q.left V⟩

end HodgeLean.Foundations.Program
