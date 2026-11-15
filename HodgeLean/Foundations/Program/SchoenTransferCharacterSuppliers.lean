import HodgeLean.Foundations.Program.SchoenTransferSuppliers
import HodgeLean.Foundations.Program.G32SelectedRealizationEigenGenerator
/-! Implication from the literal primitive-image and inverse-residual scalar equations to every embedding eigenspace.
This first character-transport piece precedes determinant expansion and the exact E1 alternating image.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxRecDepth 2048
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped TensorProduct DirectSum BigOperators CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
/-- Every embedding is transported into the exact primitive kernel with inverse residual pullback.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Remark 1.4, pp. 6–7. -/
theorem s4_e2_curve_character_transport_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier)
    (P : g32p_Part J aut S)
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    [IsIntegral (g3_power Y (2 * P.k)).left]
    [Smooth (g3_power Y (2 * P.k)).hom]
    [IsProjective (g3_power Y (2 * P.k)).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (he : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (hfaithful : Function.Injective a)
    (f : Y ⟶ P.P) (hf : Function.Injective (homPullback f 1))
    (himage : LinearMap.range (homPullback f 1) = LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (homPullback f 1 v) =
        homPullback f 1 (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v)) :
    ∀ t : cyc_Field S.m →ₐ[ℚ] ℂ,
      (cyc_eigenspace P.act.cyc_coordinates t).map ((homPullback f 1).baseChange ℂ) =
        (LinearMap.ker (Polynomial.aeval
          (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
          (Polynomial.cyclotomic S.m ℚ))).baseChange ℂ ⊓
        ⨅ u : S.H, Module.End.eigenspace
          ((homPullback (a ((QuotientGroup.mk u)⁻¹)) 1).baseChange ℂ)
          (t (g32p_fieldValue S u)) := by
  intro t
  let F := homPullback f 1
  have hinj : Function.Injective (F.baseChange ℂ) :=
    Module.Flat.lTensor_preserves_injective_linearMap F hf
  have hr : LinearMap.range (F.baseChange ℂ) = (LinearMap.range F).baseChange ℂ := by
    let E := LinearEquiv.ofInjective F hf
    have hF : F = (LinearMap.range F).subtype ∘ₗ E.toLinearMap := rfl
    rw [hF, LinearMap.baseChange_comp, LinearMap.range_comp_of_range_eq_top]
    · rfl
    · exact LinearMap.range_eq_top.mpr (E.baseChange ℚ ℂ _ _).surjective
  rw [himage] at hr
  have hc (u : S.H) :
      (homPullback (a ((QuotientGroup.mk u)⁻¹)) 1).baseChange ℂ ∘ₗ F.baseChange ℂ =
        F.baseChange ℂ ∘ₗ (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u)).baseChange ℂ := by
    have h : homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 ∘ₗ F =
        F ∘ₗ cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) :=
      LinearMap.ext (hscalar u)
    simpa only [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange ℂ) h
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨hr ▸ ⟨v, rfl⟩, ?_⟩
    apply (Submodule.mem_iInf _).mpr
    intro u
    apply Module.End.mem_eigenspace_iff.mpr
    have hs := Module.End.mem_eigenspace_iff.mp
      ((Submodule.mem_iInf _).mp hv (g32p_fieldValue S u))
    exact (LinearMap.congr_fun (hc u) v).trans (by
      change F.baseChange ℂ ((cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u)).baseChange ℂ v) = _
      rw [hs, map_smul])
  · rintro v ⟨hv, heig⟩
    obtain ⟨w, rfl⟩ := hr.symm ▸ hv
    refine ⟨w, ?_, rfl⟩
    rw [g32y_cyclotomic_eigenspace_generator]
    apply Module.End.mem_eigenspace_iff.mpr
    apply hinj
    rw [map_smul]
    obtain ⟨u, hu⟩ := S.surjective (Multiplicative.ofAdd 1)
    have hfu : g32p_fieldValue S u = IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m) := by
      simp only [g32p_fieldValue, hu, toAdd_ofAdd,
        ZMod.val_one'' (n := S.m) (by have := S.three_le; omega), pow_one]
      rfl
    rw [← hfu]
    exact (LinearMap.congr_fun (hc u) w).symm.trans
      (Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp heig u))


/-- Every embedding is transported into the exact primitive kernel with inverse residual pullback.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Remark 1.4, pp. 6–7. -/
theorem s4_e2_curve_character_transport (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier)
    (P : g32p_Part J aut S)
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    [IsIntegral (g3_power Y (2 * P.k)).left]
    [Smooth (g3_power Y (2 * P.k)).hom]
    [IsProjective (g3_power Y (2 * P.k)).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (he : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (hfaithful : Function.Injective a)
    (f : Y ⟶ P.P) (hf : Function.Injective (homPullback f 1))
    (himage : LinearMap.range (homPullback f 1) = LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (homPullback f 1 v) =
        homPullback f 1 (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v)) :
    ∀ t : cyc_Field S.m →ₐ[ℚ] ℂ,
      (cyc_eigenspace P.act.cyc_coordinates t).map ((homPullback f 1).baseChange ℂ) =
        (LinearMap.ker (Polynomial.aeval
          (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
          (Polynomial.cyclotomic S.m ℚ))).baseChange ℂ ⊓
        ⨅ u : S.H, Module.End.eigenspace
          ((homPullback (a ((QuotientGroup.mk u)⁻¹)) 1).baseChange ℂ)
          (t (g32p_fieldValue S u)) :=
  s4_e2_curve_character_transport_aux J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar

example := @s4_e2_curve_character_transport


end HodgeLean.Foundations.Program
