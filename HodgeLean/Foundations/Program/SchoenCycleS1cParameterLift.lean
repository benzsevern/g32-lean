import HodgeLean.Foundations.Program.SchoenCycleProjectiveNativeLift

/-! # Homogeneous parameter families for native projective lifts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.ComplexProjectiveSpace Filter Topology
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s2e_projective_lift_parameter_family
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k d : ℕ) (hd : Module.finrank ℂ V = k + 1)
    (p : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))
    (R : (Fin d → ℂ) → ComplexPoint
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))
    (a : (Fin d → ℂ) → (Fin (k + 1) → ℂ))
    (hlift : ∀ᶠ z in 𝓝 0, ∃ hz :
        (∑ i, a z i • Module.finBasisOfFinrankEq ℂ V hd i) ≠ 0,
      (s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd).symm (R z) =
        Projectivization.mk ℂ (∑ i, a z i • Module.finBasisOfFinrankEq ℂ V hd i) hz) :
    let b := Module.finBasisOfFinrankEq ℂ V hd
    (∑ i, a 0 i • b i) ≠ 0 ∧
    ∃ A : (Fin (k + 1) → ℂ) → ComplexPoint
        (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))),
      (∀ᶠ t in 𝓝 0, ∃ ht : (∑ i, (a 0 + t) i • b i) ≠ 0,
        A t = (s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd)
          (Projectivization.mk ℂ (∑ i, (a 0 + t) i • b i) ht)) ∧
      (∀ᶠ z in 𝓝 0, R z = A (a z - a 0)) := by
  classical
  let b := Module.finBasisOfFinrankEq ℂ V hd
  let e := b.equivFun
  let ep := s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd
  have h0 := hlift.self_of_nhds
  have ha0 : a 0 ≠ 0 := by
    intro h
    apply h0.choose
    simp only [h, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  let A : (Fin (k + 1) → ℂ) → ComplexPoint
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :=
    fun t => if h : a 0 + t ≠ 0 then vectorToComplexPoint (a 0 + t) h else p
  refine ⟨h0.choose, A, ?_, ?_⟩
  · have hn : ∀ᶠ t : Fin (k + 1) → ℂ in 𝓝 0, a 0 + t ≠ 0 :=
      (show ContinuousAt (fun t : Fin (k + 1) → ℂ => a 0 + t) 0 from
        continuousAt_const.add continuousAt_id).eventually_ne
          (by change a 0 + 0 ≠ 0; simpa only [add_zero] using ha0)
    filter_upwards [hn] with t ht
    have hsum : (∑ i, (a 0 + t) i • b i) ≠ 0 := by
      rw [← Module.Basis.equivFun_symm_apply]
      exact e.symm.map_ne_zero_iff.mpr ht
    refine ⟨hsum, ?_⟩
    dsimp only [A]
    rw [dif_pos ht]
    apply ep.symm.injective
    rw [Equiv.symm_apply_apply, s2e_finiteDimensionalProjectivePointEquiv_symm_vector]
    congr 1
    exact Module.Basis.equivFun_symm_apply b (a 0 + t)
  · filter_upwards [hlift] with z hz
    obtain ⟨hz, he⟩ := hz
    have han : a z ≠ 0 := by
      intro h
      apply hz
      simp only [h, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    have hadd : a 0 + (a z - a 0) = a z := by abel
    dsimp only [A]
    rw [hadd, dif_pos han]
    apply ep.symm.injective
    rw [he, s2e_finiteDimensionalProjectivePointEquiv_symm_vector]
    congr 1
    exact (Module.Basis.equivFun_symm_apply b (a z)).symm

end HodgeLean.Foundations.Program
