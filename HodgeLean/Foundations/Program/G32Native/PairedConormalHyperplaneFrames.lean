import HodgeLean.Foundations.Program.G32Native.PairedConormalHyperplaneCharts
import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalFrameIso
import HodgeLean.Foundations.Curves.Picard.LineBundles.CartierFrames

/-! # Regular equations and actual frames of the projective hyperplane ideal -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual affine image of the normalized projective chart. -/
def paired_hyperplaneChartOpen (k : ℕ) (i : Fin (k + 1)) :
    (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).affineOpens :=
  ⟨s2e_s2b_chart i ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion (s2e_s2b_chart i)⟩

/-- Coordinate ring identification for the actual affine chart image. -/
def paired_hyperplaneChartSectionEquiv (k : ℕ) (i : Fin (k + 1)) :
    Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ), (paired_hyperplaneChartOpen k i).1) ≃+*
      MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ :=
  ((s2e_s2b_chart i).appIso ⊤).commRingCatIsoToRingEquiv.trans
    (Scheme.ΓSpecIso ↧(MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)).commRingCatIsoToRingEquiv

/-- The normalized polynomial equation generates the original sheaf ideal
on the actual affine chart image. -/
theorem paired_hyperplaneChartIdeal_principal (k : ℕ) (i : Fin (k + 1)) :
    (s2e_hyperplaneIdeal k).ideal (paired_hyperplaneChartOpen k i) =
      Ideal.span {(paired_hyperplaneChartSectionEquiv k i).symm (paired_hyperplaneChartEquation k i)} := by
  have hc := paired_hyperplane_ideal_chart k i
  erw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    ← Ideal.map_comap_of_equiv ((s2e_s2b_chart i).appIso ⊤).commRingCatIsoToRingEquiv,
    Ideal.map_map] at hc
  change Ideal.map (paired_hyperplaneChartSectionEquiv k i).toRingHom
    ((s2e_hyperplaneIdeal k).ideal (paired_hyperplaneChartOpen k i)) = _ at hc
  have h := congrArg (Ideal.comap (paired_hyperplaneChartSectionEquiv k i).toRingHom) hc
  erw [Ideal.comap_map_of_bijective _ (paired_hyperplaneChartSectionEquiv k i).bijective] at h
  erw [← Ideal.map_comap_of_equiv (paired_hyperplaneChartSectionEquiv k i).symm,
    Ideal.map_span, Set.image_singleton] at h
  exact h

/-- Each actual affine hyperplane chart has a regular principal equation. -/
theorem paired_hyperplaneChartIdeal_regularPrincipal (k : ℕ) (i : Fin (k + 1)) :
    ∃ c : Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ), (paired_hyperplaneChartOpen k i).1),
      IsRegular c ∧ (s2e_hyperplaneIdeal k).ideal (paired_hyperplaneChartOpen k i) =
        Ideal.span {c} := by
  letI : IsDomain Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ),
      (paired_hyperplaneChartOpen k i).1) :=
    (paired_hyperplaneChartSectionEquiv k i).isDomain_iff.mpr inferInstance
  refine ⟨(paired_hyperplaneChartSectionEquiv k i).symm (paired_hyperplaneChartEquation k i),
    isRegular_iff_ne_zero.mpr ?_, paired_hyperplaneChartIdeal_principal k i⟩
  intro h
  apply paired_hyperplaneChartEquation_ne_zero k i
  have hh := congrArg (paired_hyperplaneChartSectionEquiv k i) h
  simpa only [RingEquiv.apply_symm_apply, map_zero] using hh

/-- The Cartier generator gives a rank-one frame on the actual ideal module. -/
def paired_hyperplaneIdeal_chartFrame (k : ℕ) (i : Fin (k + 1)) :
    SheafOfModules.free (R := (paired_hyperplaneChartOpen k i).1.toScheme.ringCatSheaf) PUnit ≅
      (Scheme.Modules.pullback (paired_hyperplaneChartOpen k i).1.ι).obj
        (s2c_idealModule (s2e_hyperplaneIdeal k).subschemeι) := by
  let U := paired_hyperplaneChartOpen k i
  let h := paired_hyperplaneChartIdeal_regularPrincipal k i
  let c := Classical.choose h
  have hc := Classical.choose_spec h
  let eUnit : SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) PUnit ≅
      SheafOfModules.unit U.1.toScheme.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit U.1.toScheme.ringCatSheaf)
  exact eUnit ≪≫
    (HodgeLean.Foundations.Curves.Picard.LineBundles.idealLocalGeneratorIso
      (s2e_hyperplaneIdeal k) U c hc.1 hc.2).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app
      (s2c_idealModule (s2e_hyperplaneIdeal k).subschemeι)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual affine chart images cover the entire projective model. -/
theorem paired_hyperplaneChartOpen_cover (k : ℕ) :
    ⨆ i : Fin (k + 1), (paired_hyperplaneChartOpen k i).1 = ⊤ := by
  have hU (i : Fin (k + 1)) : (paired_hyperplaneChartOpen k i).1 =
      projectiveSpaceBasicOpen k (MvPolynomial.X i) := by
    change s2e_s2b_chart i ''ᵁ ⊤ = _
    rw [Scheme.Hom.image_top_eq_opensRange]
    apply TopologicalSpace.Opens.ext
    simpa only [Scheme.Hom.coe_opensRange] using s2e_chart_range i
  simp only [hU]
  exact (pullback.snd (terminal.from (Spec ↧ℂ))
    (terminal.from (Proj (UniversalGrading.{0} k)))).iSup_preimage_eq_top
      (iSup_coordinateBasicOpen_eq_top k)

/-- The actual hyperplane ideal has rank-one frames at every scheme point. -/
theorem paired_hyperplane_ideal_frames (k : ℕ)
    (x : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)) :
    ∃ U : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Opens, x ∈ U ∧
      Nonempty (SheafOfModules.free (R := U.toScheme.ringCatSheaf) PUnit ≅
        (Scheme.Modules.pullback U.ι).obj
          (s2c_idealModule (s2e_hyperplaneIdeal k).subschemeι)) := by
  have hx : x ∈ ⨆ i : Fin (k + 1), (paired_hyperplaneChartOpen k i).1 := by
    rw [paired_hyperplaneChartOpen_cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨(paired_hyperplaneChartOpen k i).1, hi,
    ⟨paired_hyperplaneIdeal_chartFrame k i⟩⟩

/-- The actual coordinate-hyperplane ideal module on the projective model
is locally free, with the rank-one chart frames specified above. -/
theorem paired_hyperplane_ideal_locallyFree (k : ℕ) :
    (s2c_idealModule (s2e_hyperplaneIdeal k).subschemeι).IsLocallyFree := by
  apply paired_module_locallyFree_of_pullbackFrames
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := paired_hyperplane_ideal_frames k x
  exact ⟨U, hx, PUnit, ⟨e⟩⟩

end HodgeLean.Foundations.Program.G32Native
