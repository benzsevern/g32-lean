import HodgeLean.Foundations.Program.SchoenTowerL1bCommonEvaluationNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerL1bBranchIntersectionBound
import HodgeLean.Foundations.Program.SchoenTowerL1bAffineImageCoordinates
import HodgeLean.Foundations.Program.SchoenTowerL1bSimultaneousGeneratorExtension

/-! Exact generator extension on an isomorphic retained symmetric base.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained quotient extends two specified branch generators on its actual isomorphic base to etale coordinates. -/
theorem s2v_l1b_retained_base_generator_extension
    (Z B X : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    [IsIntegral X.left]
    (hdim : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (b : Fin 2 → ComplexPoint Z) (hb : b 0 ≠ b 1) (e₀ : X ≅ B)
    (I : Fin 2 → X.left.IdealSheafData)
    (hI : ∀ k, I k = (s2c_branchIdeal Z B h γ (b k)).comap e₀.hom.left)
    (p : ComplexPoint X) (hps : ∀ k, p.underlying ∈ (I k).support)
    (U₀ : X.left.affineOpens) (v : Fin 2 → Γ(X.left, U₀))
    (hpU : p ∈ Point.overOpen U₀.1)
    (hIU : ∀ k, (I k).ideal U₀ = Ideal.span {v k}) :
    ∃ (U : X.left.affineOpens) (hn : 2 ≤ h + 1)
      (z : Fin (h + 1) → Γ(X.left, U)) (hU : U.1 ≤ U₀.1),
      p ∈ Point.overOpen U.1 ∧
      (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ U.1 le_top).hom z).Etale ∧
      z ⟨0, by omega⟩ = (X.left.presheaf.map (homOfLE hU).op).hom (v 0) ∧
      z ⟨1, by omega⟩ = (X.left.presheaf.map (homOfLE hU).op).hom (v 1) ∧
      (I 0).ideal U = Ideal.span {z ⟨0, by omega⟩} ∧
      (I 1).ideal U = Ideal.span {z ⟨1, by omega⟩} := by
  obtain ⟨x, hx⟩ := hγsurj (Point.map e₀.hom p)
  have hxs (k : Fin 2) : (Point.map γ x).underlying ∈
      (s2c_branchIdeal Z B h γ (b k)).support := by
    rw [hx]
    have H := hps k
    rw [hI k, Scheme.IdealSheafData.support_comap] at H
    exact H
  have hn := s2v_l1b_branch_intersection_coordinate_bound Z B hdim h γ hγinv hγ b hb x hxs
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show h ≠ 0 by omega)
  obtain ⟨T, hT, j, q, w, hj, hq, hw, hJ⟩ :=
    s2v_l1b_common_two_branch_affine_evaluations Z B hdim n γ hγsurj hγinv hγ b hb x
  letI : IsAffine T.left := hT
  letI : IsOpenImmersion j.left := hj
  let j' := j ≫ e₀.inv
  letI : IsOpenImmersion j'.left :=
    inferInstanceAs (IsOpenImmersion (j.left ≫ e₀.inv.left))
  have hq' : Point.map j' q = p := by
    change (q ≫ j) ≫ e₀.inv = p
    rw [show q ≫ j = x ≫ γ from hq, show x ≫ γ = p ≫ e₀.hom from hx,
      Category.assoc, e₀.hom_inv_id, Category.comp_id]
  have hJ' (k : Fin 2) : ((I k).comap j'.left).ideal ⟨⊤, isAffineOpen_top T.left⟩ =
      Ideal.span {w (Sum.inl k)} := by
    have hfac : j'.left ≫ e₀.hom.left = j.left := by
      change ((j ≫ e₀.inv) ≫ e₀.hom).left = j.left
      rw [Category.assoc, e₀.inv_hom_id, Category.comp_id]
    rw [hI k, ← Scheme.IdealSheafData.comap_comp, hfac]
    exact hJ k
  obtain ⟨O, w₀, _, hpO, hEtO, hIO, _⟩ :=
    s2v_l1b_affine_image_coordinates j' w Sum.inl I hJ' hw q
  rw [hq'] at hpO
  obtain ⟨U, hU, z₀, hp, hEt, hz, hIz⟩ :=
    s2v_l1b_simultaneous_generator_extension X n I p hps O w₀ hpO hEtO hIO U₀ v hpU hIU
  let E : Fin 2 ⊕ Fin n ≃ Fin (n + 1 + 1) :=
    finSumFinEquiv.trans (finCongr (by omega))
  have hE0 : E.symm ⟨0, by omega⟩ = Sum.inl 0 := by
    apply E.symm_apply_eq.mpr
    apply Fin.ext
    rfl
  have hE1 : E.symm ⟨1, by omega⟩ = Sum.inl 1 := by
    apply E.symm_apply_eq.mpr
    apply Fin.ext
    rfl
  let z (i : Fin (n + 1 + 1)) := z₀ (E.symm i)
  refine ⟨U, hn, z, hU, hp, ?_, ?_, ?_, ?_, ?_⟩
  · exact s2v_l1b_reindex_etale _ z₀ E.symm hEt
  · change z₀ (E.symm ⟨0, by omega⟩) = _
    rw [hE0]
    exact hz 0
  · change z₀ (E.symm ⟨1, by omega⟩) = _
    rw [hE1]
    exact hz 1
  · change (I 0).ideal U = Ideal.span {z₀ (E.symm ⟨0, by omega⟩)}
    rw [hE0]
    exact hIz 0
  · change (I 1).ideal U = Ideal.span {z₀ (E.symm ⟨1, by omega⟩)}
    rw [hE1]
    exact hIz 1

end HodgeLean.Foundations.Program
