import HodgeLean.Foundations.Program.SchoenTransferQ3TangentialParameters
import HodgeLean.Adapters.NormalConeB4aGysinBridge2GermLifts

/-! Shared tangential parameters lifted to actual ambient affine sections. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing RingTheory.Sequence
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- One affine family on the target ambient scheme gives regular maximal-ideal
parameters on both support stalks via the actual embedding and etale map. -/
theorem s4_q3_etale_support_ambient_tangential_sections
    {C D W : Over (Spec ↧ℂ)} [IsIntegral D.left] [Smooth D.hom]
    (f : C ⟶ D) [Etale f.left] (j : D ⟶ W) [IsClosedImmersion j.left]
    (p : C.left) (r : ℕ) (hr : Order.coheight (f.left p) = r) :
    ∃ (U : W.left.Opens) (_ : IsAffineOpen U) (hpU : j.left (f.left p) ∈ U)
      (g : Fin r → Γ(W.left, U)),
      let rs := List.ofFn fun i => (j.left.stalkMap (f.left p)).hom
        (W.left.presheaf.germ U (j.left (f.left p)) hpU (g i))
      Ideal.ofList rs = maximalIdeal (D.left.presheaf.stalk (f.left p)) ∧
      IsRegular (D.left.presheaf.stalk (f.left p)) rs ∧
      IsRegular (C.left.presheaf.stalk p) (rs.map (f.left.stalkMap p).hom) ∧
      Ideal.ofList (rs.map (f.left.stalkMap p).hom) = maximalIdeal (C.left.presheaf.stalk p) := by
  obtain ⟨rs, hlen, hgen, hreg, hsource, hsourcegen⟩ :=
    s4_q3_etale_support_shared_parameters f p r hr
  subst r
  obtain ⟨U, hU, hpU, g, hg⟩ :=
    a3b4g_closed_immersion_affine_germ_lifts_core j.left (f.left p) rs.length rs.get
  have heq : (List.ofFn fun i => (j.left.stalkMap (f.left p)).hom
      (W.left.presheaf.germ U (j.left (f.left p)) hpU (g i))) = rs := by
    simpa only [List.ofFn_get] using congrArg List.ofFn (funext hg)
  refine ⟨U, hU, hpU, g, ?_, ?_, ?_, ?_⟩
  · rw [heq]
    exact hgen
  · rw [heq]
    exact hreg
  · rw [heq]
    exact hsource
  · rw [heq]
    exact hsourcegen

/-- The lifted tangential sections generate both support maximal ideals
through the actual section pullback along the composite support morphism. -/
theorem s4_q3_etale_support_tangential_section_pullbacks
    {C D W : Over (Spec ↧ℂ)} [IsIntegral D.left] [Smooth D.hom]
    (f : C ⟶ D) [Etale f.left] (j : D ⟶ W) [IsClosedImmersion j.left]
    (p : C.left) (r : ℕ) (hr : Order.coheight (f.left p) = r) :
    ∃ (U : W.left.Opens) (_ : IsAffineOpen U) (hpU : j.left (f.left p) ∈ U)
      (g : Fin r → Γ(W.left, U)),
      let rs := List.ofFn fun i => (j.left.stalkMap (f.left p)).hom
        (W.left.presheaf.germ U (j.left (f.left p)) hpU (g i))
      let ss := List.ofFn fun i => C.left.presheaf.germ ((f.left ≫ j.left) ⁻¹ᵁ U) p hpU
        ((f.left ≫ j.left).app U (g i))
      Ideal.ofList rs = maximalIdeal (D.left.presheaf.stalk (f.left p)) ∧
      IsRegular (D.left.presheaf.stalk (f.left p)) rs ∧
      Ideal.ofList ss = maximalIdeal (C.left.presheaf.stalk p) ∧
      IsRegular (C.left.presheaf.stalk p) ss := by
  obtain ⟨U, hU, hpU, g, hgen, hreg, hsource, hsourcegen⟩ :=
    s4_q3_etale_support_ambient_tangential_sections f j p r hr
  have heq : (List.ofFn fun i => C.left.presheaf.germ ((f.left ≫ j.left) ⁻¹ᵁ U) p hpU
      ((f.left ≫ j.left).app U (g i))) =
      (List.ofFn fun i => (j.left.stalkMap (f.left p)).hom
        (W.left.presheaf.germ U (j.left (f.left p)) hpU (g i))).map (f.left.stalkMap p).hom := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    change _ = ((j.left.stalkMap (f.left p) ≫ f.left.stalkMap p).hom
      (W.left.presheaf.germ U (j.left (f.left p)) hpU (g i)))
    rw [← Scheme.Hom.stalkMap_comp]
    exact (Scheme.Hom.germ_stalkMap_apply (f.left ≫ j.left) U p hpU (g i)).symm
  refine ⟨U, hU, hpU, g, hgen, hreg, ?_, ?_⟩
  · rw [heq]
    exact hsourcegen
  · rw [heq]
    exact hsource

end HodgeLean.Foundations.Program
