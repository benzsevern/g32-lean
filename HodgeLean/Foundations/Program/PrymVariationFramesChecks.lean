import HodgeLean.Foundations.Program.PrymVariationFramesDefs

/-! # Concrete checks of the three analytic foundations

The matrix has a moving one-dimensional kernel. The constant compact-curve
families are written in fixed fibre coordinates: the sphere has the empty frame,
and the square elliptic curve has frame `dz`. On the latter, `(1 + u) dz` has
period `1 + u` around the real generator. These calculations use explicit data
and do not invoke the eight stage 3e statements.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- A row matrix on the parameter line with a moving kernel.
Source: Lang, *Algebra*, Ch. XIII, §4, elimination for a single row. -/
def b63e_checkMatrix (u : Fin 1 → ℂ) : Matrix (Fin 1) (Fin 2) ℂ :=
  fun _ ↦ ![1, u 0]

/-- An explicit vector spanning the kernel of `b63e_checkMatrix`.
Source: Lang, *Algebra*, Ch. XIII, §4, elimination for a single row. -/
def b63e_checkVector (u : Fin 1 → ℂ) : Fin 2 → ℂ := ![-u 0, 1]

example (u : Fin 1 → ℂ) : (b63e_checkMatrix u).rank = 1 := by
  have h : LinearIndependent ℂ (b63e_checkMatrix u).row := by
    apply linearIndependent_unique_iff.mpr
    intro he
    have := congrFun he 0
    norm_num [Matrix.row, b63e_checkMatrix] at this
  exact h.rank_matrix

example (i : Fin 1) (j : Fin 2) :
    AnalyticOnNhd ℂ (fun u ↦ b63e_checkMatrix u i j) Set.univ := by
  fin_cases j
  · exact analyticOnNhd_const
  · exact (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticOnNhd _

example : AnalyticOnNhd ℂ b63e_checkVector Set.univ := by
  apply analyticOnNhd_pi_iff.mpr
  intro j
  fin_cases j
  · exact (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticOnNhd Set.univ |>.neg
  · exact analyticOnNhd_const

example (u : Fin 1 → ℂ) :
    LinearIndependent ℂ (fun _ : Fin 1 ↦ b63e_checkVector u) ∧
      Submodule.span ℂ (Set.range fun _ : Fin 1 ↦ b63e_checkVector u) =
        LinearMap.ker (b63e_checkMatrix u).mulVecLin := by
  constructor
  · apply linearIndependent_unique_iff.mpr
    intro he
    have := congrFun he 1
    norm_num [b63e_checkVector] at this
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply LinearMap.mem_ker.mpr
      ext i
      simp [b63e_checkMatrix, b63e_checkVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · intro v hv
      have he := congrFun (LinearMap.mem_ker.mp hv) 0
      have he' : v 0 + u 0 * v 1 = 0 := by
        simpa [b63e_checkMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using he
      have hv' : v = v 1 • b63e_checkVector u := by
        ext j
        fin_cases j
        · change v 0 = v 1 * (-u 0)
          linear_combination he'
        · simp [b63e_checkVector]
      rw [hv']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

-- In the constant sphere family the empty frame spans every fibre, including
-- at nonzero parameters. Its size agrees with the actual space of differentials.
example : Module.finrank ℂ (b3_HolForm ℂ (OnePoint ℂ)) = 0 ∧
    ∀ u ∈ Metric.ball (0 : ℂ) 1,
      LinearIndependent ℂ (fun i : Fin 0 ↦ (Fin.elim0 i : b3_HolForm ℂ (OnePoint ℂ))) ∧
      Submodule.span ℂ (Set.range fun i : Fin 0 ↦
        (Fin.elim0 i : b3_HolForm ℂ (OnePoint ℂ))) = ⊤ := by
  have hz : ∀ θ : b3_HolForm ℂ (OnePoint ℂ), θ = 0 := by
    intro θ
    apply Subtype.ext
    exact b4cov_sphere_form_eq_zero θ.val θ.property
  let : Subsingleton (b3_HolForm ℂ (OnePoint ℂ)) := ⟨fun θ η ↦ (hz θ).trans (hz η).symm⟩
  exact ⟨Module.finrank_zero_of_subsingleton, fun _ _ ↦ ⟨linearIndependent_empty_type, Subsingleton.elim _ _⟩⟩

-- The constant elliptic family has a nonempty frame: the actual form dz is
-- independent and spans at every parameter. Its vertical coefficient is 1.
example :
    AnalyticOnNhd ℂ (fun _ : ℂ × ℂ ↦ (1 : ℂ)) Set.univ ∧
    ∀ u ∈ Metric.ball (0 : ℂ) 1,
      LinearIndependent ℂ (fun _ : Fin 1 ↦ b3A_dz) ∧
      Submodule.span ℂ (Set.range fun _ : Fin 1 ↦ b3A_dz) = ⊤ := by
  have hp : b3_pathPeriod b3_EllipticModel b3_Elliptic b3_ellipticA b3A_dz = 1 := by
    rw [b3A_ellipticA_eq, b3A_line_pathPeriod, b3A_formFunctional_dz, b3A_φ_e0]
  have hn : b3A_dz ≠ 0 := by
    intro hz
    rw [hz] at hp
    norm_num [b3_pathPeriod, b3_pathIntegral] at hp
  have : FiniteDimensional ℂ (b3_HolForm b3_EllipticModel b3_Elliptic) :=
    b3A_holForm_finiteDimensional b3_ellipticModel_finrank
  refine ⟨analyticOnNhd_const, fun _ _ ↦ ⟨linearIndependent_unique_iff.mpr hn, ?_⟩⟩
  apply Submodule.eq_top_of_finrank_eq
  have hr : (Set.range fun _ : Fin 1 ↦ b3A_dz) = {b3A_dz} := by
    ext θ
    simp
  rw [hr, finrank_span_singleton hn, b3A_elliptic_finrank_holForm]

-- A nonzero period on the constant square elliptic curve, computed on its
-- explicit real generator, checks the normalization and the parameter variable.
example :
    (∀ u : ℂ, b3_pathPeriod b3_EllipticModel b3_Elliptic b3_ellipticA
      ((1 + u) • b3A_dz) = 1 + u) ∧
    AnalyticOnNhd ℂ (fun u : ℂ ↦
      b3_pathPeriod b3_EllipticModel b3_Elliptic b3_ellipticA
        ((1 + u) • b3A_dz)) (Metric.ball 0 1) := by
  have hp (u : ℂ) : b3_pathPeriod b3_EllipticModel b3_Elliptic b3_ellipticA
      ((1 + u) • b3A_dz) = 1 + u := by
    rw [b3A_ellipticA_eq, b3A_line_pathPeriod]
    simp [b3A_formFunctional, b3A_dz, b3A_invForm, b3A_φ_e0]
  refine ⟨hp, ?_⟩
  simp_rw [hp]
  exact analyticOnNhd_const.add analyticOnNhd_id

end HodgeLean.Foundations.Program
