import HodgeLean.Foundations.Program.SchoenTowerI2aInitialBranchChart

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- The simultaneous symmetric branch chart transports through the specified
initial-base isomorphism with its actual retained branch ideals and point.
Source: Schoen (1988), Lemma 2.2; Hartshorne, Algebraic Geometry, II.2 and II.5. -/
theorem s2v_i2a_simultaneous_initial_tower_chart
    (Z B B' : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (W : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ W),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ W, γ ≫ u = f)
    {T : Type} [Fintype T] (branch : T → ComplexPoint Z)
    (hbranch : Function.Injective branch) (e : B' ≅ B) (D : T → B'.left.IdealSheafData)
    (hD : ∀ t, D t = (s2c_branchIdeal Z B h γ (branch t)).comap e.hom.left)
    (x : ComplexPoint B') (xOrdered : ComplexPoint (g3_power Z (h + 1)))
    (hx : Point.map γ xOrdered = Point.map e.hom x) :
    ∃ (U : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (u : U ⟶ B') (p : ComplexPoint U)
      (c : MvPolynomial (Fin (h + 1)) ℂ →ₐ[ℂ] Γ(U.left, ⊤))
      (J : Finset T) (κ : J ↪ Fin (h + 1)) (z : T → Γ(U.left, ⊤)),
      IsOpenImmersion u.left ∧ Point.map u p = x ∧ c.toRingHom.Etale ∧
      (∀ t, t ∈ J ↔ x.underlying ∈ (D t).support) ∧
      (∀ t : J, z t = c (MvPolynomial.X (κ t))) ∧
      (∀ t, t ∉ J → z t = 1) ∧
      (∀ t, ((D t).comap u.left).ideal
        ⟨⊤, @isAffineOpen_top _ hU⟩ = Ideal.span {z t}) := by
  obtain ⟨U, hU, u, p, c, J, κ, z, hu, hp, hc, hJ, hz, hnone, hI⟩ :=
    s2v_i2a_simultaneous_initial_branch_chart Z B hdimZ h γ hγinv hγ branch hbranch xOrdered
  letI : IsOpenImmersion u.left := hu
  refine ⟨U, hU, u ≫ e.inv, p, c, J, κ, z,
    inferInstanceAs (IsOpenImmersion (u.left ≫ e.inv.left)), ?_, hc, ?_, hz, hnone, ?_⟩
  · apply (cancel_mono e.hom).mp
    change (p ≫ (u ≫ e.inv)) ≫ e.hom = x ≫ e.hom
    rw [Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id]
    exact hp.trans hx
  · intro t
    rw [hD, Scheme.IdealSheafData.support_comap]
    change t ∈ J ↔ (Point.map e.hom x).underlying ∈
      (s2c_branchIdeal Z B h γ (branch t)).support
    rw [← hx]
    exact hJ t
  · intro t
    rw [hD, ← Scheme.IdealSheafData.comap_comp]
    have hcomp : (u ≫ e.inv).left ≫ e.hom.left = u.left := by
      change (u.left ≫ e.inv.left) ≫ e.hom.left = u.left
      rw [Category.assoc, ← Over.comp_left, e.inv_hom_id]
      simp
    rw [hcomp]
    exact hI t

end HodgeLean.Foundations.Program
