import HodgeLean.Foundations.Curves.AbelTheorem.CurveBilinear

noncomputable section
open HodgeLean.Foundations.Program
open Module Manifold
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

theorem frame_lattice_evaluation {D : C →₀ ℤ} (F : PeriodFrame (E := E) D)
    (ell : b3_periodLattice E C) (i : Fin F.genus) :
    ell.val (F.forms i) = (F.latticeBasis.repr ell (.inl i) : ℂ) +
      ∑ j, (F.latticeBasis.repr ell (.inr j) : ℂ) * loopIntegral (F.b j) (F.forms i) := by
  classical
  let ev : b3_periodLattice E C →ₗ[ℤ] ℂ :=
    (LinearMap.proj (F.forms i)).comp (b3_periodLattice E C).subtype.toIntLinearMap
  have hl (j : Fin F.genus) : (F.latticeBasis (.inl j)).val (F.forms i) =
      if j = i then 1 else 0 := by
    rw [F.a_basis]
    exact F.normalized j i
  have hr (j : Fin F.genus) : (F.latticeBasis (.inr j)).val (F.forms i) =
      loopIntegral (F.b j) (F.forms i) := by rw [F.b_basis]; rfl
  calc
    ell.val (F.forms i) =
        ∑ s, (F.latticeBasis.repr ell s : ℂ) * (F.latticeBasis s).val (F.forms i) := by
      have he := congrArg ev (F.latticeBasis.sum_repr ell)
      simp only [map_sum, map_smul, zsmul_eq_mul] at he
      change (∑ s, (F.latticeBasis.repr ell s : ℂ) *
        (F.latticeBasis s).val (F.forms i)) = ell.val (F.forms i) at he
      exact he.symm
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp only [hl, hr, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]

end HodgeLean.Foundations.Curves.AbelTheorem
