import HodgeLean.Foundations.Program.PathCoverFamilyDefs

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

theorem b65z_period_multiplicities {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) :
    Module.finrank ℂ (b4_HomG b63d_naturalRep
      (fun a ↦ b4_cplxAct ℂ (C := b65z_fibre c D.C t) a)
      (b3_periodF ℂ (b65z_fibre c D.C t))) = 3 ∧
    Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep b63d_naturalRep)
      (fun a ↦ b4_cplxAct ℂ (C := b65z_fibre c D.C t) a)
      (b3_periodF ℂ (b65z_fibre c D.C t))) = 3 := by
  have hq : Function.Injective (b6_branch t.val) :=
    (b6t_polydisc_neighbourhood c D.atlas.hb).2.2.2 t.property
  have hrank : (∑ i : Fin 13, ((b4b_toMatrix (g i) - 1).rank : ℝ)) = 14 := by
    have h := g32h_multCW_of_nielsen _ hg
    unfold g32h_multCW at h
    have hz : (∑ i : Fin 13, ((b4b_toMatrix (g i) - 1).rank : ℤ)) = 14 := by
      linarith
    exact_mod_cast hz
  have hbar : (∑ i : Fin 13,
      b4_age (HurwitzPrymRex_barRep b63d_naturalRep (g i))) = 7 := by
    simp only [b63d_conjugateRep_age]
    have h := g32h_holoCW_of_nielsen _ hg
    unfold g32h_holoCW at h
    linarith
  have hnat : (∑ i : Fin 13, b4_age (b63d_naturalRep (g i))) = 7 := by
    have hsum : (∑ i : Fin 13,
        b4_age (HurwitzPrymRex_barRep b63d_naturalRep (g i))) +
        (∑ i : Fin 13, b4_age (b63d_naturalRep (g i))) = 14 := by
      rw [← Finset.sum_add_distrib, ← hrank]
      apply Finset.sum_congr rfl
      intro i hi
      rw [HurwitzPrymRex_age_add_bar, b63d_naturalRep_rank]
    linarith
  rw [b4_hodge_eq_holo (by simp) (D.hG t), b4_hodge_eq_holo (by simp) (D.hG t)]
  constructor
  · have h := b63d_finite_holoCW (b65z_fibre c D.C t) (D.hG t)
      (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t)
      (D.hk t) (D.hsurj t) (D.hgal t) (b6_branch t.val) hq g
      (D.hbranch t) (D.hrot t) b63d_naturalRep b63d_naturalRep_nontrivial
    rw [hnat, b63d_naturalRep_finrank] at h
    norm_num at h
    exact_mod_cast h
  · have h := b63d_finite_holoCW (b65z_fibre c D.C t) (D.hG t)
      (b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t)
      (D.hk t) (D.hsurj t) (D.hgal t) (b6_branch t.val) hq g
      (D.hbranch t) (D.hrot t) (HurwitzPrymRex_barRep b63d_naturalRep)
      b63d_conjugateRep_nontrivial
    rw [hbar, b63d_conjugateRep_finrank] at h
    norm_num at h
    exact_mod_cast h

theorem b65z_lattice_basis {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) :
    Nonempty (Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) t)) := by
  let Y := b65z_fibre c D.C t
  letI : Module.Finite ℤ (b3_periodLattice ℂ Y) := b3_periodLattice_finite (by simp)
  letI : Module.Free ℤ (b3_periodLattice ℂ Y) := b3_periodLattice_free
  letI : Module.Finite ℤ (b63l_periodLattice Y) := inferInstance
  letI : Module.Free ℤ (b63l_periodLattice Y) := inferInstance
  have hd := b63d_saturated_dimensions Y (D.hG t) (b65z_period_multiplicities hg D t)
  let β := Module.finBasisOfFinrankEq ℤ (b63l_periodLattice Y) hd.1
  obtain ⟨P, hP, hOp, E, hE⟩ := b63l_period_image_comparison Y (D.hG t)
  let E' : b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) t ≃ₗ[ℤ]
      b63l_periodLattice Y := E
  exact ⟨β.map E'.symm⟩


theorem b65z_eigen_rank {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (s t : b6t_polydisc c) :
    Module.finrank ℂ ↥(b63e_transportedF c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t ⊓
        Module.End.eigenspace (b2_cplxMap (b63g2_operator c D.C D.hC (b6t_polydisc c) (Subset.refl _) s).toAddMonoidHom)
          (HodgeBlocks.WeilAction.omegaC 3)) = 3 ∧
      Module.finrank ℂ ↥(b63e_transportedF c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t ⊓
        Module.End.eigenspace (b2_cplxMap (b63g2_operator c D.C D.hC (b6t_polydisc c) (Subset.refl _) s).toAddMonoidHom)
          (-HodgeBlocks.WeilAction.omegaC 3)) = 3 := by
  obtain ⟨E, hE, hF⟩ := b63e_lattice_period_transport c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.hG D.P D.hP s t
  have hCW := b63d_saturated_eigen_ranks (b65z_fibre c D.C t) (D.hG t)
    (b65z_period_multiplicities hg D t)
  let centreOp := b63g2_centre c D.C D.hC (b6t_polydisc c) (Subset.refl _) s
  let ι := (b63l_periodLattice (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t)).subtype
  let Z := (b4b_centreAct (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t) (D.hG t)).toIntLinearMap
  have hι : Function.Injective (ι.baseChange ℂ) :=
    Module.Flat.lTensor_preserves_injective_linearMap ι
      (b63l_periodLattice (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t)).subtype_injective
  have hc : ∀ x, ι (E (centreOp x)) = Z (ι (E x)) := by
    intro x
    change (E (centreOp x)).val = Z (E x).val
    rw [hE, hE]
    change D.P t (b6m_H1Equiv _ (b63d_centre c D.C D.hC (b6t_polydisc c) (Subset.refl _) s x.val)) =
      Z (D.P t (b6m_H1Equiv _ x.val))
    rw [b63d_centre_transport c D.C D.hC (b6t_polydisc c) (Subset.refl _) t s,
      b63g2_period_centre c D.C D.hC (b6t_polydisc c) (Subset.refl _) t (D.hG t) (D.P t) (D.hP t)]
    rfl
  have hJ : (b63g2_operator c D.C D.hC (b6t_polydisc c) (Subset.refl _) s).toAddMonoidHom.toIntLinearMap =
      LinearMap.id + centreOp + centreOp := by
    ext x
    simp [b63g2_operator, centreOp, two_smul, add_assoc]
  have key := b63g2_eigen_transfer E ι hι centreOp _ Z hJ hc (b3_periodF ℂ _) g32h_omega _
    b63g2_one_add_two_omega
  have key2 := b63g2_eigen_transfer E ι hι centreOp _ Z hJ hc (b3_periodF ℂ _) (star g32h_omega) _
    b63g2_one_add_two_star_omega
  have h1 : Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t) (D.hG t) g32h_omega) =
      3 := hCW.1
  have k1 : Module.finrank ℂ ↥((((b3_periodF ℂ (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t)).comap
      (ι.baseChange ℂ)) ⊓ (LinearMap.ker (Z.baseChange ℂ - g32h_omega • LinearMap.id)).comap
        (ι.baseChange ℂ))) = 3 := h1
  have g1 := key.trans k1
  have hF' : b63e_transportedF c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t =
      (((b3_periodF ℂ (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t)).comap (ι.baseChange ℂ)).comap
        ((E : b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s →ₗ[ℤ]
          b63l_periodLattice (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t)).baseChange ℂ)) := hF
  rw [hF']
  have h2 : Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t) (D.hG t)
      (star g32h_omega)) = 3 := hCW.2
  have k2 : Module.finrank ℂ ↥((((b3_periodF ℂ (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t)).comap
      (ι.baseChange ℂ)) ⊓ (LinearMap.ker (Z.baseChange ℂ - star g32h_omega • LinearMap.id)).comap
        (ι.baseChange ℂ))) = 3 := h2
  exact ⟨g1, key2.trans k2⟩


theorem b65z_period_eigen_ranks {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (s t : b6t_polydisc c) :
    Module.finrank ℂ ↥(b63e_transportedF c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t ⊓
        Module.End.eigenspace ((D.A s).baseChange ℂ) (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 ∧
      Module.finrank ℂ ↥(b63e_transportedF c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t ⊓
        Module.End.eigenspace ((D.A s).baseChange ℂ) (Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
  obtain ⟨E, hEv, hE⟩ := b63e_lattice_period_transport c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.hG D.P D.hP s t
  let T := b6m_H1Equiv (b6m_transport c D.C ⟨s.val, (Subset.refl _) s.property⟩ ⟨t.val, (Subset.refl _) t.property⟩)
  have hAtransport : ∀ x, (E ((D.A s) x)).val =
      b63d_periodOperator (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t) (D.hG t) (E x).val := by
    intro x
    rw [hEv, hEv]
    change D.P t (T ((D.A s) x).val) = b63d_periodOperator _ (D.hG t) (D.P t (T x.val))
    rw [(D.hA s) x]
    simp only [b63d_operator, LinearMap.add_apply, LinearMap.id_apply,
      LinearMap.smul_apply, map_add, b63d_periodOperator]
    have hc : T (b63d_centre c D.C D.hC (b6t_polydisc c) (Subset.refl _) s x.val) = b63d_centre c D.C D.hC (b6t_polydisc c) (Subset.refl _) t (T x.val) :=
      b63d_centre_transport c D.C D.hC (b6t_polydisc c) (Subset.refl _) t s x.val
    change D.P t (T x.val) + D.P t (T ((2 : ℕ) • b63d_centre c D.C D.hC (b6t_polydisc c) (Subset.refl _) s x.val)) =
      D.P t (T x.val) + (2 : ℕ) • b4b_centreAct _ (D.hG t) (D.P t (T x.val))
    rw [map_nsmul, map_nsmul, hc,
      b63g2_period_centre c D.C D.hC (b6t_polydisc c) (Subset.refl _) t (D.hG t) (D.P t) (D.hP t)]
  have hcw := b63d_saturated_eigen_ranks (b65z_fibre c D.C t) (D.hG t)
    (b65z_period_multiplicities hg D t)
  have hEC : (E.baseChange ℤ ℂ (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s)
      (b63l_periodLattice (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t))).toLinearMap =
      (E : b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s →ₗ[ℤ]
        b63l_periodLattice (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t)).baseChange ℂ := rfl
  have key (z : ℂ) := b64b_period_eigen_rank _ (D.hG t) E (D.A s) hAtransport z
  have hsub : b63e_transportedF c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t =
      (b63l_periodF (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t)).comap
        (E.baseChange ℤ ℂ (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s)
          (b63l_periodLattice (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t))).toLinearMap :=
    hE.trans (congrArg (fun φ => (b63l_periodF (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t)).comap φ)
      hEC.symm)
  rw [hsub]
  have key' (z w : ℂ) (h : 1 + 2 * z = w) :
      Module.finrank ℂ ↥((b63l_periodF (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t)).comap
        (E.baseChange ℤ ℂ (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s)
          (b63l_periodLattice (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t))).toLinearMap ⊓
        Module.End.eigenspace ((D.A s).baseChange ℂ) w) =
      Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre c D.C (b6t_polydisc c) (Subset.refl _) t) (D.hG t) z) := by
    subst h
    exact key z
  exact ⟨(key' _ _ b64b_conjugate_root_eigenvalue).trans hcw.2,
    (key' _ _ b64b_root_eigenvalue).trans hcw.1⟩

end HodgeLean.Foundations.Program
