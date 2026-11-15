import HodgeLean.Foundations.Program.G32Native.CoefficientCoordinateEquiv
import HodgeLean.Foundations.Program.G32Native.ContinuousLinearRecovery
import HodgeLean.Foundations.BundleThom.ImmersionDefs
import HodgeLean.Foundations.Program.G32Native.SmoothConormalPointFrame

/-! # Inverse continuity from finite actual normal frames -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Bundle Topology
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native

/-- For a fibrewise linear comparison with the original coefficient subspaces,
forward continuity implies inverse continuity in the actual normal topology. -/
theorem canonicalCoefficientEquiv_inverse_continuous (G : CanonicalAbelGeometry)
    (E : ∀ x : ComplexPoint G.Q, canonicalNormalFibre G x ≃ₗ[ℂ]
      (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator)
    (hE : @Continuous
      (TotalSpace (Fin G.k → ℂ) (canonicalNormalFibre G))
      (TotalSpace (Fin G.k → ℂ)
        (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator))
      (normalEvaluationTopology (Conormal.sheaf G.ι.left) G.k) (coefficientTotalTopology G)
      (fun z => ⟨z.proj, E z.proj z.2⟩)) :
    @Continuous
      (TotalSpace (Fin G.k → ℂ)
        (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator))
      (TotalSpace (Fin G.k → ℂ) (canonicalNormalFibre G))
      (coefficientTotalTopology G) (normalEvaluationTopology (Conormal.sheaf G.ι.left) G.k)
      (fun z => ⟨z.proj, (E z.proj).symm z.2⟩) := by
  let N := TotalSpace (Fin G.k → ℂ) (canonicalNormalFibre G)
  let C := TotalSpace (Fin G.k → ℂ)
    (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator)
  letI : TopologicalSpace N := normalEvaluationTopology (Conormal.sheaf G.ι.left) G.k
  letI : TopologicalSpace C := coefficientTotalTopology G
  let f : N → C := fun z => ⟨z.proj, E z.proj z.2⟩
  let g : C → N := fun z => ⟨z.proj, (E z.proj).symm z.2⟩
  change Continuous f at hE
  change Continuous g
  have hbC : Continuous (fun z : C => z.proj) :=
    ((continuous_coefficientTotal_coordinates_iff G id).mp continuous_id).1
  have hcC : Continuous (fun z : C => coefficientCoordinateEquiv G.k z.2.1) := by
    apply continuous_pi
    intro j
    apply (((continuous_coefficientTotal_coordinates_iff G id).mp continuous_id).2 j).congr
    intro z
    exact (coefficientCoordinateEquiv_apply G.k z.2.1 j).symm
  apply continuous_iff_continuousAt.mpr
  intro z₀
  obtain ⟨U, hxU, ⟨e⟩⟩ := s2e_smooth_closedImmersion_conormal_frames
    G.Q G.W G.k G.k G.ι z₀.proj.underlying
  let e' := (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app
    (Conormal.sheaf G.ι.left) ≪≫ e
  let H := i1_normalFrameHomeomorph G.ι.left G.k U e'
  let B := ↥(Point.overOpen U : Set (ComplexPoint G.Q))
  let L (y : B) := (i1_conormalFrameBasis G.ι.left G.k U e' y.1 y.2).dualBasis.equivFun.symm
  let A : B → (Fin G.k → ℂ) →L[ℂ] (Fin (G.k + 1) → ℂ) := fun y =>
    ((coefficientCoordinateEquiv G.k).toLinearMap.comp
      ((g32n_homogeneousLine G.k G.eQ y.1).submodule.dualAnnihilator.subtype.comp
        ((E y.1).toLinearMap.comp (L y).toLinearMap))).toContinuousLinearMap
  have hA : Continuous A := by
    apply continuous_clm_apply.mpr
    intro v
    let src : B → N := fun y => (H.symm (y, v)).1
    have hs : Continuous src := continuous_subtype_val.comp
      (H.symm.continuous.comp (continuous_id.prodMk continuous_const))
    have hc := ((continuous_coefficientTotal_coordinates_iff G (f ∘ src)).mp (hE.comp hs)).2
    apply continuous_pi
    intro j
    change Continuous (fun y => coefficientCoordinateEquiv G.k ((E y.1) (L y v)).1 j)
    apply (hc j).congr
    intro y
    change ((E y.1) (L y v)).1 (Pi.single j 1) =
      coefficientCoordinateEquiv G.k ((E y.1) (L y v)).1 j
    exact (coefficientCoordinateEquiv_apply G.k _ j).symm
  have hAi : ∀ y, Function.Injective (A y) := by
    intro y v w h
    change coefficientCoordinateEquiv G.k ((E y.1) (L y v)).1 =
      coefficientCoordinateEquiv G.k ((E y.1) (L y w)).1 at h
    exact (L y).injective ((E y.1).injective
      (Subtype.val_injective ((coefficientCoordinateEquiv G.k).injective h)))
  let S := {z : C | z.proj ∈ Point.overOpen U}
  let b : S → B := fun z => ⟨z.1.proj, z.2⟩
  let v : S → (Fin G.k → ℂ) := fun z => (L (b z)).symm ((E z.1.proj).symm z.1.2)
  have hb : Continuous b := (hbC.comp continuous_subtype_val).subtype_mk _
  have himage : (fun z : S => A (b z) (v z)) =
      (fun z : S => coefficientCoordinateEquiv G.k z.1.2.1) := by
    funext z
    change coefficientCoordinateEquiv G.k
      ((E z.1.proj) (L (b z) ((L (b z)).symm ((E z.1.proj).symm z.1.2)))).1 = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hv : Continuous v := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply continuousAt_of_continuous_linear_image (fun z => A (b z)) v z
      (hA.comp hb).continuousAt (hAi (b z))
    rw [himage]
    exact (hcC.comp continuous_subtype_val).continuousAt
  have hlocal : Continuous (fun z : S => g z.1) := by
    have hh := continuous_subtype_val.comp (H.symm.continuous.comp (hb.prodMk hv))
    apply hh.congr
    intro z
    change (⟨z.1.proj, L (b z) ((L (b z)).symm ((E z.1.proj).symm z.1.2))⟩ : N) = _
    rw [LinearEquiv.apply_symm_apply]
  have hU : IsOpen {z : C | z.proj ∈ Point.overOpen U} :=
    (Point.isOpen_overOpen U).preimage hbC
  exact (continuousOn_iff_continuous_restrict.mpr hlocal).continuousAt
    (hU.mem_nhds hxU)

#print axioms canonicalCoefficientEquiv_inverse_continuous
end HodgeLean.Foundations.Program.G32Native
