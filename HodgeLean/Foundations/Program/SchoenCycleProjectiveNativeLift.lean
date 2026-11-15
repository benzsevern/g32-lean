import HodgeLean.Foundations.Program.SchoenCycleProjectiveSectionEvaluation
import HodgeLean.Foundations.Program.SchoenCycleNativeSectionDifferential
import HodgeLean.Foundations.Program.SchoenCycleNativeGermComparison

/-! # Analytic homogeneous lifts in native projective coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.ComplexProjectiveSpace Filter Topology
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Native coordinates on projective space have an analytic homogeneous lift.
Source: Hartshorne, Algebraic Geometry, II.7, standard projective charts. -/
theorem s2e_projective_native_analytic_homogeneous_lift
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k d : ℕ) (hd : Module.finrank ℂ V = k + 1)
    [SmoothOfRelativeDimension d
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom]
    (p : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))) :
    ∃ a : (Fin d → ℂ) → (Fin (k + 1) → ℂ), AnalyticAt ℂ a 0 ∧
      (∀ᶠ z in 𝓝 0, ∃ hz : (∑ i, a z i • Module.finBasisOfFinrankEq ℂ V hd i) ≠ 0,
        (s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd).symm
          ((localChart (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) d p).symm
            (localChart (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) d p p + z)) =
          Projectivization.mk ℂ (∑ i, a z i • Module.finBasisOfFinrankEq ℂ V hd i) hz) := by
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let C := localChart PP d p
  let r := fun z : Fin d → ℂ => C.symm (C p + z)
  have hr0 : r 0 = p := by
    dsimp only [r]
    rw [add_zero, C.left_inv (mem_localChart_source PP d p)]
  have hr : Tendsto r (𝓝 0) (𝓝 p) := s2e_centered_native_chart_tendsto PP d p
  obtain ⟨i, U, v, hU, hp, hv, he⟩ := s2e_projectivePoint_local_normalized_section k p
  let b := Module.finBasisOfFinrankEq ℂ V hd
  let a := fun z => v (r z)
  have hmem : ∀ᶠ z in 𝓝 0, r z ∈ U := hr (hU.mem_nhds hp)
  have hpU : p.underlying ∈ (s2e_standardProjectiveAffineOpen i).1 := by
    obtain ⟨hi, hn, hh⟩ := he p hp
    rw [← hh]
    exact s2e_standardProjectiveAffineOpen_mem (v p) i (hi.trans_ne one_ne_zero)
  have ha : AnalyticAt ℂ a 0 := by
    apply AnalyticAt.pi
    intro j
    let L : V →ₗ[ℂ] ℂ := b.coord j
    have hs := s2e_native_section_analytic PP d p (s2e_standardProjectiveAffineOpen i).1 hpU
      (s2e_standardProjectiveLinearSection V k hd L i)
    apply hs.congr
    filter_upwards [hmem] with z hz
    obtain ⟨hi, hn, hh⟩ := he (r z) hz
    change Point.evaluate _ _ (r z) = a z j
    rw [← hh, s2e_standardProjectiveLinearSection_evaluate V k hd L (v (r z)) i
      (hi.trans_ne one_ne_zero), hi, inv_one, one_mul]
    change b.coord j (∑ l, v (r z) l • b l) = v (r z) j
    rw [← Module.Basis.equivFun_symm_apply]
    exact congrFun (b.equivFun.apply_symm_apply (v (r z))) j
  refine ⟨a, ha, ?_⟩
  filter_upwards [hmem] with z hz
  obtain ⟨hi, hn, hh⟩ := he (r z) hz
  have hsum : (∑ j, a z j • b j) ≠ 0 := by
    rw [← Module.Basis.equivFun_symm_apply]
    exact b.equivFun.symm.map_ne_zero_iff.mpr hn
  refine ⟨hsum, ?_⟩
  change (s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd).symm (r z) =
    Projectivization.mk ℂ (∑ j, a z j • b j) hsum
  rw [← hh, s2e_finiteDimensionalProjectivePointEquiv_symm_vector]
  congr 1
  exact Module.Basis.equivFun_symm_apply b (a z)

end HodgeLean.Foundations.Program
