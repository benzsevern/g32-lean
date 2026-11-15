import HodgeLean.Foundations.Program.SchoenTransferQ3SharedCoordinateMorphisms
import HodgeLean.Foundations.Program.SchoenTransferQ3TangentialDominance

/-! Dense smooth base opens for the actual common ambient tangential morphism. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Topology
namespace HodgeLean.Foundations.Program

/-- The actual common tangential sections furnish dominant ambient maps
and dense base opens on which both specified ambient maps are smooth. -/
theorem s4_q3_actual_generic_tangential_maps
    {C D X W : Over (Spec ↧ℂ)} (r : ℕ) [SmoothOfRelativeDimension r D.hom]
    [IsIntegral X.left] [Smooth X.hom] [IsIntegral W.left] [Smooth W.hom]
    (f : C ⟶ D) [Etale f.left] (i : C ⟶ X) (j : D ⟶ W)
    [IsClosedImmersion j.left] (q : X ⟶ W) [IsFinite q.left]
    (hsquare : i ≫ q = f ≫ j) (p : C.left) :
    ∃ (U : W.left.Opens) (_ : IsAffineOpen U) (_ : j.left (f.left p) ∈ U)
      (g : Fin r → Γ(W.left, U)),
      let h := s4_q3_tangentialCoordinateMorphism W U r g
      IsDominant h ∧ IsDominant ((q.left ∣_ U) ≫ h) ∧
      ∃ A B : (ComplexPoint.complexAffineSpace (Fin r)).Opens,
        Dense (A : Set (ComplexPoint.complexAffineSpace (Fin r))) ∧
        Dense (B : Set (ComplexPoint.complexAffineSpace (Fin r))) ∧
        Smooth (h ∣_ A) ∧ Smooth (((q.left ∣_ U) ≫ h) ∣_ B) := by
  obtain ⟨U, hU, hpU, g, V, hpV, hVU, hCi, htarget, hsource⟩ :=
    s4_q3_shared_support_coordinate_morphisms r f i j q hsquare p
  let WU := ComplexPoint.openScheme W U
  let XU := ComplexPoint.openScheme X (q.left ⁻¹ᵁ U)
  let T : Over (Spec ↧ℂ) :=
    Over.mk (ComplexPoint.complexAffineSpace (Fin r) ↘ Spec ↧ℂ)
  letI : IsIntegral T.left := inferInstanceAs (IsIntegral (ComplexPoint.complexAffineSpace (Fin r)))
  let h : WU ⟶ T := Over.homMk (s4_q3_tangentialCoordinateMorphism W U r g)
    (s4_q3_tangentialCoordinateMorphism_over W U r g)
  let qU : XU ⟶ WU := Over.homMk (q.left ∣_ U) (by
    change (q.left ∣_ U) ≫ U.ι ≫ W.hom = (q.left ⁻¹ᵁ U).ι ≫ X.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w q])
  letI : Nonempty U.toScheme := ⟨⟨j.left (f.left p), hpU⟩⟩
  letI : Nonempty (q.left ⁻¹ᵁ U).toScheme := ⟨⟨i.left p, hCi hpV⟩⟩
  letI : Nonempty V.toScheme := ⟨⟨f.left p, hpV⟩⟩
  letI : Nonempty (f.left ⁻¹ᵁ V).toScheme := ⟨⟨p, hpV⟩⟩
  letI : IsAffine U.toScheme := hU
  letI : IsAffine WU.left := inferInstanceAs (IsAffine U.toScheme)
  letI : IsAffine XU.left := hU.preimage q.left
  letI : IsAffine T.left := inferInstanceAs (IsAffine (ComplexPoint.complexAffineSpace (Fin r)))
  letI : QuasiCompact h.left := inferInstance
  letI : QuasiCompact (qU ≫ h).left := inferInstance
  letI : IsIntegral WU.left := inferInstanceAs (IsIntegral U.toScheme)
  letI : IsIntegral XU.left := inferInstanceAs (IsIntegral (q.left ⁻¹ᵁ U).toScheme)
  letI : Smooth WU.hom := inferInstanceAs (Smooth (U.ι ≫ W.hom))
  letI : Smooth XU.hom := inferInstanceAs (Smooth ((q.left ⁻¹ᵁ U).ι ≫ X.hom))
  letI : LocallyOfFiniteType (h.left ≫ T.hom) := by rw [Over.w h]; infer_instance
  letI : LocallyOfFiniteType h.left := locallyOfFiniteType_of_comp h.left T.hom
  letI : LocallyOfFiniteType ((qU ≫ h).left ≫ T.hom) := by
    rw [Over.w (qU ≫ h)]; infer_instance
  letI : LocallyOfFiniteType (qU ≫ h).left := locallyOfFiniteType_of_comp _ T.hom
  letI : Etale (j.left.resLE U V hVU ≫ h.left) := htarget
  letI : Etale (i.left.resLE (q.left ⁻¹ᵁ U) (f.left ⁻¹ᵁ V) hCi ≫ (qU ≫ h).left) := hsource
  obtain ⟨hdW, A, hA, hsW⟩ := s4_q3_generic_smooth_of_etale_support WU T h V.toScheme
    (j.left.resLE U V hVU)
  obtain ⟨hdX, B, hB, hsX⟩ := s4_q3_generic_smooth_of_etale_support XU T (qU ≫ h)
    (f.left ⁻¹ᵁ V).toScheme (i.left.resLE (q.left ⁻¹ᵁ U) (f.left ⁻¹ᵁ V) hCi)
  exact ⟨U, hU, hpU, g, hdW, hdX, A, B, hA, hB, hsW, hsX⟩

end HodgeLean.Foundations.Program
