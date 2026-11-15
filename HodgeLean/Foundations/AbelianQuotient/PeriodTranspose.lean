import HodgeLean.Foundations.AbelianQuotient.IntegralInverse

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- A rational character of the period lattice is determined by its values on the S12 basis. -/
private theorem addMonoidHom_apply_eq_sum_basis (χ : abelianPeriodLattice X →+ ℚ)
    (l : abelianPeriodLattice X) :
    χ l = ∑ i, ((abelianLatticeBasis X).repr l i : ℚ) * χ (abelianLatticeBasis X i) := by
  conv_lhs => rw [← (abelianLatticeBasis X).sum_repr l]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, zsmul_eq_mul]


end HodgeLean.Foundations.AbelianQuotient

namespace HodgeLean.Foundations.AbelianQuotient
variable (X : Variety)
theorem period_transpose (Y : Variety) (T : HQ X.X 1 →ₗ[ℚ] HQ Y.X 1) :
    ∃ N : ℕ, 0 < N ∧ ∃ φ : abelianPeriodLattice Y.X →+ abelianPeriodLattice X.X, ∀ x l,
      abelianPeriod Y.X ((N : ℚ) • T x) l = abelianPeriod X.X x (φ l) := by
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv X.X
  obtain ⟨eY, heY⟩ := spec_abelianPeriod_equiv Y.X
  set b := abelianLatticeBasis X.X
  set c := abelianLatticeBasis Y.X
  let δ : Fin (2 * dim X.X.left) → (abelianPeriodLattice X.X →+ ℚ) := fun i =>
    (Int.castAddHom ℚ).comp (b.coord i).toAddMonoidHom
  have hδ : ∀ χ : abelianPeriodLattice X.X →+ ℚ, χ = ∑ i, χ (b i) • δ i := by
    intro χ
    ext l
    rw [addMonoidHom_apply_eq_sum_basis X.X χ l, AddMonoidHom.finsetSum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [δ, b, mul_comm]
  let M : Fin (2 * dim X.X.left) → Fin (2 * dim Y.X.left) → ℚ := fun i j =>
    eY (T (e.symm (δ i))) (c j)
  let N : ℕ := ∏ i, ∏ j, (M i j).den
  have hN : 0 < N := Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => (M i j).den_pos
  have hK : ∀ i j, ∃ k : ℤ, (k : ℚ) = N * M i j := by
    intro i j
    obtain ⟨c, hc⟩ : (M i j).den ∣ N :=
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ j, (M i j).den) (Finset.mem_univ i))
    refine ⟨(M i j).num * c, ?_⟩
    rw [hc]
    push_cast
    rw [← Rat.mul_den_eq_num (M i j)]
    ring
  choose K hK using hK
  let φ : abelianPeriodLattice Y.X →+ abelianPeriodLattice X.X :=
    (c.constr ℤ fun j => ∑ i, K i j • b i).toAddMonoidHom
  refine ⟨N, hN, φ, fun x l => ?_⟩
  rw [map_smul, Pi.smul_apply, smul_eq_mul, ← heY, ← he]
  have h1 : eY (T x) l = ∑ i, e x (b i) * ∑ j, (c.repr l j : ℚ) * M i j := by
    conv_lhs => rw [← e.symm_apply_apply x, hδ (e x)]
    simp only [map_sum, map_smul, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [addMonoidHom_apply_eq_sum_basis Y.X _ l]
  have h2 : e x (φ l) = ∑ j, (c.repr l j : ℚ) * ∑ i, (K i j : ℚ) * e x (b i) := by
    simp only [φ, LinearMap.toAddMonoidHom_coe, Module.Basis.constr_apply_fintype,
      Module.Basis.equivFun_apply, map_sum, map_zsmul, zsmul_eq_mul]
  rw [h1, h2]
  simp only [hK, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring


end HodgeLean.Foundations.AbelianQuotient
