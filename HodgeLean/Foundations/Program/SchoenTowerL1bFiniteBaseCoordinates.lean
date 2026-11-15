import HodgeLean.Foundations.Program.SchoenTowerL1bFiniteSupportedCoordinates
import HodgeLean.Foundations.Program.SchoenTowerL1bFiniteAffineImage
import HodgeLean.Foundations.Program.SchoenTowerL1bAbsentBranchRefinement

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Simultaneous marked-branch coordinates transport through a retained base isomorphism, with all absent supports removed. -/
theorem s2v_l1b_finite_base_coordinates
    (Z B X : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom] [IsIntegral B.left] [Smooth B.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (m : ℕ) (b : Fin m → ComplexPoint Z) (hb : Function.Injective b)
    (e : X ≅ B) (D : Fin m → X.left.IdealSheafData)
    (hD : ∀ t, D t = (s2c_branchIdeal Z B h γ (b t)).comap e.hom.left)
    (x : ComplexPoint X) :
    ∃ (U : X.left.affineOpens) (z : Fin (h + 1) → Γ(X.left, U))
      (f : {t : Fin m // x.underlying ∈ (D t).support} ↪ Fin (h + 1)),
      x.underlying ∈ U.1 ∧
      (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ U.1 le_top).hom z).Etale ∧
      (∀ t, (D t.val).ideal U = Ideal.span {z (f t)}) ∧
      (∀ t, x.underlying ∉ (D t).support → (D t).ideal U = ⊤) := by
  classical
  obtain ⟨xp, hxp⟩ := hγsurj (Point.map e.hom x)
  obtain ⟨A, hA, j, p, w, f, hj, hp, hEt, hI⟩ :=
    s2v_l1b_finite_supported_coordinates Z B hdim h γ hγsurj hγinv hγ m b hb xp
  letI : IsAffine A.left := hA
  letI : IsOpenImmersion j.left := hj
  let v : A ⟶ X := j ≫ e.inv
  let κ := {t : Fin m // x.underlying ∈ (D t).support}
  have hsupport (t : κ) : (Point.map γ xp).underlying ∈
      (s2c_branchIdeal Z B h γ (b t.val)).support := by
    rw [hxp]
    have H := t.property
    rw [hD, Scheme.IdealSheafData.support_comap] at H
    exact H
  let f' : κ ↪ Fin (h + 1) :=
    ⟨fun t => f ⟨t.val, hsupport t⟩, by
      intro t s H
      have H' := congrArg Subtype.val (f.injective H)
      exact Subtype.ext H'⟩
  have hpv : Point.map v p = x := by
    apply (cancel_mono e.hom).mp
    change (p ≫ (j ≫ e.inv)) ≫ e.hom = x ≫ e.hom
    rw [Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id]
    exact hp.trans hxp
  have hIv (t : κ) : ((D t.val).comap v.left).ideal
      ⟨⊤, isAffineOpen_top A.left⟩ = Ideal.span {w (f' t)} := by
    rw [hD, ← Scheme.IdealSheafData.comap_comp]
    have hv : v.left ≫ e.hom.left = j.left := by
      change (j.left ≫ e.inv.left) ≫ e.hom.left = j.left
      rw [Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.comp_id]
    rw [hv]
    exact hI ⟨t.val, hsupport t⟩
  letI : IsOpenImmersion v.left := inferInstanceAs (IsOpenImmersion (j.left ≫ e.inv.left))
  obtain ⟨U, z, hpre, hpx, hzEt, hzI, _⟩ :=
    s2v_l1b_finite_affine_image_coordinates v w f' (fun t : κ => D t.val) hIv hEt p
  rw [hpv] at hpx
  obtain ⟨V, hVU, hpV, hVEt, hVtop⟩ :=
    s2v_l1b_absent_branch_refinement X D x U hpx z hzEt
  let r := (X.left.presheaf.map (homOfLE hVU).op).hom
  refine ⟨V, (fun i => r (z i)), f', hpV, hVEt, ?_, hVtop⟩
  intro t
  rw [← (D t.val).map_ideal hVU, hzI t, Ideal.map_span, Set.image_singleton]
  rfl

end HodgeLean.Foundations.Program
