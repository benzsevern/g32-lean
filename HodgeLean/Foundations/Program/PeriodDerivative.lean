import HodgeLean.Foundations.Program.PeriodDerivativeProofs

/-! # B6-6a: graph and period derivatives
Implication from differentiable frame blocks and invertible head to graph derivatives,
and from marked filtration frames to derivatives of the retained period function.
Kodaira–Spencer, duality, multiplication and jet comparisons are later stages.
HC no distance; AV milestone no distance.
-/
noncomputable section
open scoped TensorProduct Matrix Topology
open HodgeLean.Papers Filter Set
namespace HodgeLean.Foundations.Program
attribute [local instance] b64c_RootFamily.topC b64c_RootFamily.chartC b64c_RootFamily.manC
  b64c_RootFamily.t2C b64c_RootFamily.compactC b64c_RootFamily.connectedC
  b64c_RootFamily.actionC b64c_RootFamily.totalChart b64c_RootFamily.totalMan
  b64c_RootFamily.fibreChart b64c_RootFamily.fibreMan b64c_RootFamily.fibreT2
  b64c_RootFamily.fibreCompact b64c_RootFamily.fibreConnected b64c_RootFamily.fibreFaithful

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful


/-- The directional graph derivative is the block quotient rule.
Source: Griffiths–Harris, Principles of Algebraic Geometry, Ch. 1, §5;
Mathlib differential calculus; `b64_local_subframe`, `b64i_chart`. -/
theorem b66_fderiv_graphCoord (u : (Fin 10 → ℂ) → Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (t₀ : Fin 10 → ℂ)
    (hh : DifferentiableAt ℂ (fun t => b64_headBlock (u t)) t₀)
    (ht : DifferentiableAt ℂ (fun t => b64_tailBlock (u t)) t₀)
    (hi : IsUnit (b64_headBlock (u t₀))) :
    DifferentiableAt ℂ (fun t => b64_graphCoord (u t)) t₀ ∧
    ∀ h, fderiv ℂ (fun t => b64_graphCoord (u t)) t₀ h =
      b60c_matrixCoordinates (b66_graphVariation u t₀ h) :=
  b66_fderiv_graphCoord_aux u t₀ hh ht hi

example := @b66_fderiv_graphCoord

/-- The graph derivative in the standard nine by ten convention.
Source: Griffiths–Harris, Principles of Algebraic Geometry, Ch. 1, §5;
Mathlib differential calculus; `b64_local_subframe`, `b64i_chart`. -/
theorem b66_graphCoord_toMatrix (u : (Fin 10 → ℂ) → Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (t₀ : Fin 10 → ℂ)
    (hh : DifferentiableAt ℂ (fun t => b64_headBlock (u t)) t₀)
    (ht : DifferentiableAt ℂ (fun t => b64_tailBlock (u t)) t₀)
    (hi : IsUnit (b64_headBlock (u t₀))) :
    LinearMap.toMatrix' (fderiv ℂ (fun t => b64_graphCoord (u t)) t₀).toLinearMap =
      b66_variationMatrix u t₀ :=
  b66_graphCoord_toMatrix_aux u t₀ hh ht hi

example := @b66_graphCoord_toMatrix

/-- A local subframe computes the derivative of a chart filtration.
Source: Griffiths–Harris, Principles of Algebraic Geometry, Ch. 1, §5;
Mathlib differential calculus; `b64_local_subframe`, `b64i_chart`. -/
theorem b66_coordOf_local_derivative {ι : Type*} [Fintype ι]
    (u : (Fin 10 → ℂ) → ι → ℂ ⊗[ℤ] b60_Lattice)
    (F : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice))
    (W : Set (Fin 10 → ℂ)) (hW : IsOpen W)
    (hu : ∀ k p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr (u t k) p) W)
    (hs : ∀ t ∈ W, Submodule.span ℂ (Set.range (u t)) = F t)
    (hc : ∀ t ∈ W, ∃ z, F t = b60_F z)
    (t₀ : Fin 10 → ℂ) (h₀ : t₀ ∈ W) :
    ∃ W' : Set (Fin 10 → ℂ), IsOpen W' ∧ t₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ σ : Fin 3 → ι,
        (∀ t ∈ W', IsUnit (b64_headBlock (fun j => b64_negPart (u t (σ j)))) ∧
          Submodule.span ℂ (Set.range (fun j => b64_negPart (u t (σ j)))) =
            F t ⊓ b64_Eminus) ∧
        ∀ h, fderiv ℂ (fun t => b64_coordOf (F t)) t₀ h =
          b60c_matrixCoordinates
            (b66_graphVariation (fun t j => b64_negPart (u t (σ j))) t₀ h) :=
  b66_coordOf_local_derivative_aux u F W hW hu hs hc t₀ h₀

example := @b66_coordOf_local_derivative

/-- The retained period has the same derivative as its marked negative frame.
Source: Griffiths–Harris, Principles of Algebraic Geometry, Ch. 1, §5;
Mathlib differential calculus; `b64_local_subframe`, `b64i_chart`. -/
theorem b66_period_frame_derivative (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (v : (Fin 10 → ℂ) → Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (t₀ : Fin 10 → ℂ) (h₀ : t₀ ∈ b6t_polydisc mr_base)
    (hv : ∀ᶠ t in 𝓝 t₀, Submodule.span ℂ (Set.range (v t)) =
      b64c_markedF _ m (rf8_transportedFamily R s) t ⊓ b64_Eminus) :
    fderiv ℂ (b64i_period R s m) t₀ =
      fderiv ℂ (fun t => b64_graphCoord (v t)) t₀ :=
  b66_period_frame_derivative_aux R s m hJ hpol v t₀ h₀ hv

example := @b66_period_frame_derivative

/-- The retained period derivative in the codifferential matrix convention.
Source: Griffiths–Harris, Principles of Algebraic Geometry, Ch. 1, §5;
Mathlib differential calculus; `b64_local_subframe`, `b64i_chart`. -/
theorem b66_period_toMatrix (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (v : (Fin 10 → ℂ) → Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (t₀ : Fin 10 → ℂ) (h₀ : t₀ ∈ b6t_polydisc mr_base)
    (hv : ∀ᶠ t in 𝓝 t₀, Submodule.span ℂ (Set.range (v t)) =
      b64c_markedF _ m (rf8_transportedFamily R s) t ⊓ b64_Eminus)
    (hh : DifferentiableAt ℂ (fun t => b64_headBlock (v t)) t₀)
    (ht : DifferentiableAt ℂ (fun t => b64_tailBlock (v t)) t₀) :
    LinearMap.toMatrix' (fderiv ℂ (b64i_period R s m) t₀).toLinearMap =
      b66_variationMatrix v t₀ :=
  b66_period_toMatrix_aux R s m hJ hpol v t₀ h₀ hv hh ht

example := @b66_period_toMatrix

/-- The test plane has rank three at every point, using existing chart computations. -/
example (z : Fin 9 → ℂ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (b64_negFrame z))) = 3 := by
  rw [← b64_negFrame_span]
  exact (b60_weil_dimensions z).2

/-- Invertibility is checked directly for a varying family. -/
example (z : Fin 9 → ℂ) : b64_headBlock (b64_negFrame z) = 1 := by
  ext i j
  rw [b64_headBlock, Matrix.of_apply, b64_negFrame_repr, Matrix.one_apply]
  simp [Prod.ext_iff, Fin.ext_iff, eq_comm]
  refine (Finset.sum_eq_zero fun x _ => ?_).symm
  rw [ite_eq_right_iff]
  intro h
  omega

/-- All nine graph directions occur in this ten-parameter family. -/
example : Function.Surjective
    (fun t : Fin 10 → ℂ => b64_graphCoord (b64_negFrame (fun i => t i.castSucc))) := by
  intro z
  refine ⟨fun j => if h : j.val < 9 then z ⟨j.val, h⟩ else 0, ?_⟩
  dsimp only
  rw [b64_graphCoord_negFrame]
  ext i
  simp

/-- The moving frame has analytic eigen-coordinates, without any new open body. -/
example (j : Fin 3) (p : Fin 2 × Fin 6) :
    AnalyticOnNhd ℂ (fun t : Fin 10 → ℂ =>
      b60c_eigenBasis.repr (b64_negFrame (fun i => t i.castSucc) j) p) Set.univ := by
  intro t _
  simp only [b64_negFrame_repr, g32m_toMat, Matrix.of_apply]
  apply AnalyticAt.add analyticAt_const
  apply Finset.analyticAt_fun_sum
  intro k _
  exact ((ContinuousLinearMap.proj (finProdFinEquiv (k, j)).castSucc :
    (Fin 10 → ℂ) →L[ℂ] ℂ).analyticAt t).mul analyticAt_const


/-- Chain check: the array supplied here can replace the derivative array between
arbitrary basis changes in `g32r_PeriodMap.codiff`. -/
example (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (v : (Fin 10 → ℂ) → Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (t₀ : Fin 10 → ℂ) (h₀ : t₀ ∈ b6t_polydisc mr_base)
    (hv : ∀ᶠ t in 𝓝 t₀, Submodule.span ℂ (Set.range (v t)) =
      b64c_markedF _ m (rf8_transportedFamily R s) t ⊓ b64_Eminus)
    (hh : DifferentiableAt ℂ (fun t => b64_headBlock (v t)) t₀)
    (ht : DifferentiableAt ℂ (fun t => b64_tailBlock (v t)) t₀)
    (L : Matrix (Fin 9) (Fin 9) ℂ) (T : Matrix (Fin 10) (Fin 10) ℂ) :
    L * LinearMap.toMatrix' (fderiv ℂ (b64i_period R s m) t₀).toLinearMap * T =
      L * b66_variationMatrix v t₀ * T := by
  rw [b66_period_toMatrix R s m hJ hpol v t₀ h₀ hv hh ht]

end HodgeLean.Foundations.Program
