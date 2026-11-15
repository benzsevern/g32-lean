import HodgeLean.Foundations.Program.SchoenCycleU1ProjectionChartAvoidance
import HodgeLean.Adapters.IntersectionProductProjectionUnramified

/-! # Finite projections unramified near a finite divisor support -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A single actual finite projective projection is unramified on affine
neighbourhoods of every point in a prescribed finite support.
Source: HodgeLean, `a3r_generic_finite` and
`IntersectionProductScaf_generic_projection_unramified_neighborhood`;
Shafarevich, Basic Algebraic Geometry 1, I.5.3, Theorem 1.15. -/
theorem s2e_u1_finite_projection_unramified_on_support
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {n : ℕ} (hn : Order.height (genericPoint X.left) = n) (S : Finset X.left) :
    ∃ π : X ⟶ a3h_PnO n, IsFinite π.left ∧
      ∀ x ∈ S, ∃ (A : CommRingCat) (j : Spec A ⟶ X.left),
        IsOpenImmersion j ∧ x ∈ Set.range j ∧ FormallyUnramified (j ≫ π.left) := by
  have hF := a3r_generic_finite (a3s_IX X) (a3s_IX_isHomogeneous X)
    (a3h_dim_cone X n hn)
  have hU := a3r_generic_iInter S _ (fun x _ =>
    IntersectionProductScaf_generic_projection_unramified_neighborhood X hn x)
  obtain ⟨a, ha, hu⟩ := (hF.inter hU).nonempty
  refine ⟨a3h_πO X ha, inferInstance, ?_⟩
  intro x hx
  exact hu x hx ha

/-- The same projection can put every prescribed support point in its first
standard affine chart while remaining unramified near all those points.
Source: HodgeLean, `a3r_generic_finite`,
`IntersectionProductScaf_generic_projection_unramified_neighborhood`, and
`s2e_u1_generic_projection_coordinate_notMem`. -/
theorem s2e_u1_finite_projection_support_in_one_chart
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {n : ℕ} (hn : Order.height (genericPoint X.left) = n) (S : Finset X.left) :
    ∃ π : X ⟶ a3h_PnO n, IsFinite π.left ∧
      (∀ x ∈ S, π.left x ∈ Set.range (a3m_Pnκ n 0)) ∧
      ∀ x ∈ S, ∃ (A : CommRingCat) (j : Spec A ⟶ X.left),
        IsOpenImmersion j ∧ x ∈ Set.range j ∧ FormallyUnramified (j ≫ π.left) := by
  classical
  have hF := a3r_generic_finite (a3s_IX X) (a3s_IX_isHomogeneous X)
    (a3h_dim_cone X n hn)
  have hU := a3r_generic_iInter S _ (fun x _ =>
    IntersectionProductScaf_generic_projection_unramified_neighborhood X hn x)
  have hV : a3r_Generic {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ |
      ∀ x ∈ S, a3r_lin (a3r_mat a) (MvPolynomial.X 0) ∉ (a3s_CX X).prime x} := by
    apply a3r_generic_iInter
    intro x _
    letI : ((a3s_CX X).prime x).IsPrime := (a3s_CX X).isPrime_prime x
    apply s2e_u1_generic_projection_coordinate_notMem
    obtain ⟨j, p, hp⟩ := (a3s_CX X).cover x
    refine ⟨j, ?_⟩
    intro hj
    exact ((a3s_CX X).X_mem_prime_iff x j).mp hj ⟨p, hp⟩
  obtain ⟨a, ⟨ha, hu⟩, hv⟩ := ((hF.inter hU).inter hV).nonempty
  refine ⟨a3h_πO X ha, inferInstance, ?_, ?_⟩
  · intro x hx
    have hnot : MvPolynomial.X (0 : Fin (n + 1)) ∉
        (a3m_projCharts n).prime ((a3h_πO X ha).left x) := by
      change MvPolynomial.X (0 : Fin (n + 1)) ∉
        (a3m_projCharts n).prime (a3h_π X ha x)
      rw [a3h_prime_π]
      exact hv x hx
    by_contra h
    exact hnot (((a3m_projCharts n).X_mem_prime_iff _ 0).mpr h)
  · intro x hx
    exact hu x hx ha

/-- Every finite support on a smooth integral projective complex scheme is
contained in an actual affine open.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5, affine standard opens;
HodgeLean, `s2e_u1_finite_projection_support_in_one_chart`. -/
theorem s2e_u1_exists_affine_open_containing_support
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Finset X.left) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U := by
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (X := X) (genericPoint X.left)
  obtain ⟨π, hπ, hS, _⟩ := s2e_u1_finite_projection_support_in_one_chart X hn S
  letI : IsFinite π.left := hπ
  refine ⟨π.left ⁻¹ᵁ (a3m_Pnκ n 0).opensRange,
    (isAffineOpen_opensRange (a3m_Pnκ n 0)).preimage π.left, ?_⟩
  intro x hx
  exact hS x hx

end HodgeLean.Foundations.Program
