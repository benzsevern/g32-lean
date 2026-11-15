import HodgeLean.Foundations.Program.G32SelectedRealizationImage

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

set_option maxHeartbeats 400000 in
set_option maxRecDepth 2048 in
theorem g32x_lattice_factorization {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    ∃ j : b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c) →+
        g32x_L D t,
    ∃ p : g32x_L D t →+
        b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c),
      (∀ l, j (p l) = b4_groupEnd ℂ (C := b65z_fibre c D.C t) b4b_projectorCoeff l) ∧
      (∀ l, p (j l) = (116640 : ℕ) • l) ∧
      b63e_transportedF c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) D.P (b65z_s₀ c) t ≤
        (b3_periodF ℂ (b65z_fibre c D.C t)).comap (b2_cplxMap j) ∧
      b3_periodF ℂ (b65z_fibre c D.C t) ≤
        (b63e_transportedF c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) D.P
          (b65z_s₀ c) t).comap (b2_cplxMap p) := by
  let M := b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c)
  let L := g32x_L D t
  let F := b3_periodF ℂ (b65z_fibre c D.C t)
  let FM := b63e_transportedF c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
    D.P (b65z_s₀ c) t
  let U : L →+ L := b4_groupEnd ℂ (C := b65z_fibre c D.C t) b4b_projectorCoeff
  obtain ⟨E, hE, _⟩ := b63e_lattice_period_transport c D.C D.hC (b6t_polydisc c)
    (Set.Subset.refl _) D.hG D.P D.hP (b65z_s₀ c) t
  obtain ⟨pS, hpS, hpSj⟩ := g32x_saturated_projector_retraction U.toIntLinearMap
    b4b_projectorDenominator (g32x_groupEnd_square (b65z_fibre c D.C t) (D.hG t))
  let j : M →+ L := (b63e_transportMap c D.C D.hC (b6t_polydisc c)
    (Set.Subset.refl _) D.P (b65z_s₀ c) t).toAddMonoidHom
  let p : L →+ M := E.symm.toAddMonoidHom.comp pS.toAddMonoidHom
  have hj : j = (b63l_periodLattice (b65z_fibre c D.C t)).subtype.toAddMonoidHom.comp
      E.toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro l
    exact (hE l).symm
  have hjp (l : L) : j (p l) = U l := by
    rw [hj]
    change (E (E.symm (pS l))).val = U l
    rw [LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun hpS l

  have hpj (l : M) : p (j l) = (116640 : ℕ) • l := by
    rw [hj]
    change E.symm (pS (E l).val) = _
    rw [hpSj, E.symm.map_smul, E.symm_apply_apply]
    exact Nat.cast_smul_eq_nsmul ℤ 116640 l
  have hjF : FM ≤ F.comap (b2_cplxMap j) := le_rfl
  have hpF : F ≤ FM.comap (b2_cplxMap p) := by
    change F ≤ (F.comap (b2_cplxMap j)).comap (b2_cplxMap p)
    rw [← Submodule.comap_comp, ← b63g_cplxMap_comp]
    have hcomp : j.comp p = U := AddMonoidHom.ext hjp
    rw [hcomp]
    exact b4_groupEnd_periodF (D.hG t) b4b_projectorCoeff
  exact ⟨j, p, hjp, hpj, hjF, hpF⟩

end HodgeLean.Foundations.Program
