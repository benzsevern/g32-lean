import HodgeLean.Foundations.Program.SchoenTransferQ3CoordinateSupportRefinement
import HodgeLean.Foundations.Program.SchoenTransferQ3TangentialBaseCut
import HodgeLean.Foundations.Program.SchoenTransferQ3RetainedSmoothBase

/-! Constructed common smooth tangential neighbourhood of the retained support generic point. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Topology
namespace HodgeLean.Foundations.Program

/-- The actual etale support square constructs a common smooth tangential
neighbourhood, retaining the original support generic point and every
cartesian ambient support square. -/
theorem s4_q3_common_smooth_tangential_support_neighbourhood
    {C D X W : Over (Spec ↧ℂ)} [IsIntegral C.left] [IsIntegral D.left]
    [IsIntegral X.left] [IsIntegral W.left] [Smooth C.hom] [Smooth D.hom]
    [Smooth X.hom] [Smooth W.hom] (r : ℕ) [SmoothOfRelativeDimension r D.hom]
    (i : C ⟶ X) (j : D ⟶ W) [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (f : C ⟶ D) [Etale f.left] (q : X ⟶ W) [IsFinite q.left] [Flat q.left]
    (hsquare : i ≫ q = f ≫ j) :
    ∃ (C' D' X' W' T : Over (Spec ↧ℂ))
      (bC : C' ⟶ C) (bD : D' ⟶ D) (aX : X' ⟶ X) (aW : W' ⟶ W)
      (i' : C' ⟶ X') (j' : D' ⟶ W') (f' : C' ⟶ D') (q' : X' ⟶ W') (h : W' ⟶ T),
      IsOpenImmersion bC.left ∧ IsOpenImmersion bD.left ∧
      IsOpenImmersion aX.left ∧ IsOpenImmersion aW.left ∧
      IsClosedImmersion i'.left ∧ IsClosedImmersion j'.left ∧
      IsFinite q'.left ∧ Flat q'.left ∧ Etale f'.left ∧
      i' ≫ q' = f' ≫ j' ∧ aX ≫ q = q' ≫ aW ∧
      Smooth h.left ∧ Smooth (q' ≫ h).left ∧
      Etale (j' ≫ h).left ∧ Etale (i' ≫ q' ≫ h).left ∧
      Smooth C'.hom ∧ Smooth D'.hom ∧ Smooth X'.hom ∧ Smooth W'.hom ∧
      Smooth T.hom ∧ SmoothOfRelativeDimension r T.hom ∧
      IsPullback i'.left bC.left aX.left i.left ∧
      IsPullback j'.left bD.left aW.left j.left ∧
      IsPullback q'.left aX.left aW.left q.left ∧
      ∃ c : C'.left, bC.left c = genericPoint C.left := by
  obtain ⟨U, hU, hpU, g, V, hpV, hVU, hCi, hEtD, _, _, _, A, hdA, hsW, hsX⟩ :=
    s4_q3_retained_shared_smooth_tangential_base r f i j q hsquare (genericPoint C.left)
  let T₀ : Over (Spec ↧ℂ) := Over.mk (complexAffineSpace (Fin r) ↘ Spec ↧ℂ)
  let h₀ : openScheme W U ⟶ T₀ := Over.homMk (s4_q3_tangentialCoordinateMorphism W U r g)
    (s4_q3_tangentialCoordinateMorphism_over W U r g)
  have hV : Smooth (V.ι ≫ D.hom) := inferInstance
  obtain ⟨B, hBU, hBV, i₁, j₁, f₁, q₁, H₁, hsq₁, hi₁, hj₁, hq₁,
    hiClosed₁, hjClosed₁, hfinite₁, hflat₁, heF₁, hsH₁, hsQH₁, heJ₁, _, hsD₁, hsC₁,
    hcartI₁, hcartJ₁, hcartQ₁⟩ :=
    s4_q3_coordinate_support_ambient_refinement i j f q hsquare U V hVU h₀ hEtD hV A hsW hsX
  let C₁ := openScheme C (f.left ⁻¹ᵁ V)
  let D₁ := openScheme D V
  let X₁ := openScheme X (q.left ⁻¹ᵁ B)
  let W₁ := openScheme W B
  let bC₁ := openInclusion C (f.left ⁻¹ᵁ V)
  let bD₁ := openInclusion D V
  let aX₁ := openInclusion X (q.left ⁻¹ᵁ B)
  let aW₁ := openInclusion W B
  let c₁ : C₁.left := ⟨genericPoint C.left, hpV⟩
  letI : Nonempty C₁.left := ⟨c₁⟩
  letI : Nonempty (f.left ⁻¹ᵁ V).toScheme := ⟨c₁⟩
  letI : Nonempty D₁.left := ⟨f₁.left c₁⟩
  letI : Nonempty V.toScheme := ⟨⟨f.left (genericPoint C.left), hpV⟩⟩
  letI : IsIntegral C₁.left := isIntegral_of_isOpenImmersion (f.left ⁻¹ᵁ V).ι
  letI : IsIntegral D₁.left := isIntegral_of_isOpenImmersion V.ι
  letI : Nonempty X₁.left := ⟨i₁.left c₁⟩
  letI : Nonempty (q.left ⁻¹ᵁ B).toScheme := ⟨i₁.left c₁⟩
  letI : Nonempty W₁.left := ⟨q₁.left (i₁.left c₁)⟩
  letI : Nonempty B.toScheme := ⟨q₁.left (i₁.left c₁)⟩
  letI : IsIntegral X₁.left := isIntegral_of_isOpenImmersion (q.left ⁻¹ᵁ B).ι
  letI : IsIntegral W₁.left := isIntegral_of_isOpenImmersion B.ι
  letI : Smooth X₁.hom := inferInstanceAs (Smooth ((q.left ⁻¹ᵁ B).ι ≫ X.hom))
  letI : Smooth W₁.hom := inferInstanceAs (Smooth (B.ι ≫ W.hom))
  letI : Smooth C₁.hom := hsC₁
  letI : Smooth D₁.hom := hsD₁
  letI : IsClosedImmersion i₁.left := hiClosed₁
  letI : IsClosedImmersion j₁.left := hjClosed₁
  letI : IsFinite q₁.left := hfinite₁
  letI : Flat q₁.left := hflat₁
  letI : Etale f₁.left := heF₁
  letI : Etale (j₁ ≫ H₁).left := heJ₁
  letI : IsIntegral T₀.left := inferInstanceAs (IsIntegral (complexAffineSpace (Fin r)))
  obtain ⟨B₂, hB₂A, hB₂S, hgen₂, i₂, j₂, f₂, q₂, H₂, hsq₂, hi₂, hj₂, hq₂,
    hf₂, hqraw₂, hiClosed₂, hjClosed₂, hfinite₂, hflat₂, heF₂, hsH₂, hsQH₂, heJ₂, heI₂,
    hsD₂, hsC₂, hcartI₂, hcartJ₂, hcartQ₂⟩ :=
    s4_q3_retained_tangential_base_cut i₁ j₁ f₁ q₁ H₁ hsq₁ A hdA hsH₁ hsQH₁
  let S₂ := j₁.left ⁻¹ᵁ (H₁.left ⁻¹ᵁ A)
  let C₂ := openScheme C₁ (f₁.left ⁻¹ᵁ S₂)
  let D₂ := openScheme D₁ S₂
  let X₂ := openScheme X₁ (q₁.left ⁻¹ᵁ B₂)
  let W₂ := openScheme W₁ B₂
  let T₂ := openScheme T₀ A
  let bC₂ := openInclusion C₁ (f₁.left ⁻¹ᵁ S₂)
  let bD₂ := openInclusion D₁ S₂
  let aX₂ := openInclusion X₁ (q₁.left ⁻¹ᵁ B₂)
  let aW₂ := openInclusion W₁ B₂
  let bC := bC₂ ≫ bC₁
  let bD := bD₂ ≫ bD₁
  let aX := aX₂ ≫ aX₁
  let aW := aW₂ ≫ aW₁
  have hopenC : IsOpenImmersion bC.left := by
    change IsOpenImmersion ((f₁.left ⁻¹ᵁ S₂).ι ≫ (f.left ⁻¹ᵁ V).ι)
    infer_instance
  have hopenD : IsOpenImmersion bD.left := by
    change IsOpenImmersion (S₂.ι ≫ V.ι)
    infer_instance
  have hopenX : IsOpenImmersion aX.left := by
    change IsOpenImmersion ((q₁.left ⁻¹ᵁ B₂).ι ≫ (q.left ⁻¹ᵁ B).ι)
    infer_instance
  have hopenW : IsOpenImmersion aW.left := by
    change IsOpenImmersion (B₂.ι ≫ B.ι)
    infer_instance
  have hcartI : IsPullback i₂.left bC.left aX.left i.left := hcartI₂.paste_vert hcartI₁
  have hcartJ : IsPullback j₂.left bD.left aW.left j.left := hcartJ₂.paste_vert hcartJ₁
  have hcartQ : IsPullback q₂.left aX.left aW.left q.left := hcartQ₂.paste_vert hcartQ₁
  have hambient : aX ≫ q = q₂ ≫ aW := by
    apply Over.OverMorphism.ext
    exact hcartQ.w.symm
  letI : IsOpenImmersion bC₁.left := inferInstanceAs (IsOpenImmersion (f.left ⁻¹ᵁ V).ι)
  letI : IsDominant bC₁.left :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace bC₁.left bC₁.left.isOpenMap⟩
  have hgeneric₁ : bC₁.left (genericPoint C₁.left) = genericPoint C.left :=
    s2_dominant_genericPoint bC₁.left
  let c₂ : C₂.left := ⟨genericPoint C₁.left, hgen₂⟩
  have hgen : bC.left c₂ = genericPoint C.left := hgeneric₁
  letI : SmoothOfRelativeDimension r T₀.hom := by
    change SmoothOfRelativeDimension r (complexAffineSpace (Fin r) ↘ Spec ↧ℂ)
    exact AffineSpace.smoothOfRelativeDimension_of_card_eq (n := Fin r) (Spec ↧ℂ) (by simp)
  letI : Smooth T₀.hom := SmoothOfRelativeDimension.smooth r T₀.hom
  have hdimT : SmoothOfRelativeDimension r T₂.hom := by
    change SmoothOfRelativeDimension r (A.ι ≫ T₀.hom)
    have hh : SmoothOfRelativeDimension (0 + r) (A.ι ≫ T₀.hom) := inferInstance
    simpa only [Nat.zero_add] using hh
  have hsT : Smooth T₂.hom := inferInstanceAs (Smooth (A.ι ≫ T₀.hom))
  have hsX₂ : Smooth X₂.hom := inferInstanceAs (Smooth ((q₁.left ⁻¹ᵁ B₂).ι ≫ X₁.hom))
  have hsW₂ : Smooth W₂.hom := inferInstanceAs (Smooth (B₂.ι ≫ W₁.hom))
  exact ⟨C₂, D₂, X₂, W₂, T₂, bC, bD, aX, aW, i₂, j₂, f₂, q₂, H₂,
    hopenC, hopenD, hopenX, hopenW, hiClosed₂, hjClosed₂, hfinite₂, hflat₂, heF₂,
    hsq₂, hambient, hsH₂, hsQH₂, heJ₂, heI₂, hsC₂, hsD₂, hsX₂, hsW₂,
    hsT, hdimT, hcartI, hcartJ, hcartQ, c₂, hgen⟩

end HodgeLean.Foundations.Program
