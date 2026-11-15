import HodgeLean.Foundations.Program.G32Native.PairedC3AffineFrame
import HodgeLean.Foundations.Program.SchoenCycleS3ConormalOnCharts

/-! # Local rank-k frames from affine regular equations on the same subscheme -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program RingTheory.Sequence

/-- Regular equations on actual ambient affine charts supply precisely the
local affine conormal frames of the closed subscheme.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8. -/
theorem paired_c3_local_frames_of_regular_charts
    {X : Scheme.{0}} (I : X.IdealSheafData) (k : ℕ)
    (hcharts : ∀ x : I.subscheme,
      ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ X) (_ : IsOpenImmersion j),
        I.subschemeι x ∈ j.opensRange ∧
        ∃ f : Fin k → A, IsWeaklyRegular A (List.ofFn f) ∧
          Ideal.map (Scheme.ΓSpecIso A).hom.hom
            ((I.comap j).ideal ⟨⊤, isAffineOpen_top _⟩) = Ideal.span (Set.range f)) :
    ∀ x : I.subscheme, ∃ (U : I.subscheme.Opens), x ∈ U ∧ IsAffine U.toScheme ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj (s2c_conormal I.subschemeι) ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules)) := by
  intro x
  obtain ⟨A, j, hj, hx, f, hreg, hI⟩ := hcharts x
  letI := hj
  let U := I.subschemeι ⁻¹ᵁ j.opensRange
  have hf : Nonempty (Scheme.Modules.restrict (s2c_conormal I.subschemeι) U.ι ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules)) := by
    apply s2e_subschemeConormal_free_on_chart I j (Fin k)
    dsimp only
    rw [hI]
    exact ⟨pairedC3AffineConormalFrame f hreg⟩
  obtain ⟨q, hq, _, hqr⟩ := s2e_subschemeQuotientChart I j
  letI := hq
  have hr : Set.range q = Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact congrArg (fun W : I.subscheme.Opens => (W : Set I.subscheme)) hqr
  let e := IsOpenImmersion.isoOfRangeEq q U.ι hr
  refine ⟨U, hx, IsAffine.of_isIso e.inv, ?_⟩
  obtain ⟨ef⟩ := hf
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app _ ≪≫ ef⟩

#print axioms paired_c3_local_frames_of_regular_charts
end HodgeLean.Foundations.Program.G32Native
