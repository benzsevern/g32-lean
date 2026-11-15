import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairProjectiveChartFormula
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5FiniteBooleanFamilies

/-! Boolean matrix images of projective Zariski loci.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
open HodgeLean.Foundations.Program
namespace HodgeLean.WitnessSelection.StageTwo

/-- A projective Zariski locus has an exact Boolean description in real matrix coordinates.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_projective_locus_formula {n : ℕ}
    (C : Set (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ))) (hC : IsClosed C) :
    ∃ f : s2v_t11b_Formula (Fintype.card
      ((Fin (n + 1) × Fin (n + 1)) ⊕ (Fin (n + 1) × Fin (n + 1)))),
      ∀ z, z ∈ f.realize ↔
        ∃ p : Projectivization ℂ (Fin (n + 1) → ℂ),
          (ComplexProjectiveSpace.projectivizationToComplexPoint p).underlying ∈ C ∧
          z = s2e_pair_projectiveRealMatrix n p := by
  classical
  choose b hb using fun i => s2e_pair_projective_chart_formula C hC i
  obtain ⟨f, hf⟩ := s2v_hardt_cad5_finite_union_formula b
  refine ⟨f, ?_⟩
  intro z
  rw [hf, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨v, hv, _, hc, hz⟩ := (hb i z).mp hi
    exact ⟨Projectivization.mk ℂ v hv, hc, hz⟩
  · rintro ⟨p, hc, rfl⟩
    induction p using Projectivization.ind with
    | _ v hv =>
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h
        exact hv (funext (fun i => by simpa using not_not.mp (not_exists.mp h i)))
      let w := (v i)⁻¹ • v
      have hw : w ≠ 0 := smul_ne_zero (inv_ne_zero hi) hv
      have hwi : w i = 1 := by simp [w, hi]
      have he : Projectivization.mk ℂ w hw = Projectivization.mk ℂ v hv :=
        (Projectivization.mk_eq_mk_iff' ℂ w v hw hv).mpr ⟨(v i)⁻¹, rfl⟩
      refine ⟨i, (hb i _).mpr ⟨w, hw, hwi, ?_, ?_⟩⟩
      · change (ComplexProjectiveSpace.projectivizationToComplexPoint
          (Projectivization.mk ℂ w hw)).underlying ∈ C
        rwa [he]
      · exact congrArg (s2e_pair_projectiveRealMatrix n) he.symm

end HodgeLean.WitnessSelection.StageTwo
