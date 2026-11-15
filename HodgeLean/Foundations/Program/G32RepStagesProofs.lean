import HodgeLean.Foundations.Program.G32RepStagesDefs
import HodgeLean.Adapters.F1575Theta

/-! # Open bodies for the first G32 representation stages

One auxiliary declaration per statement of `G32RepStages.lean`. The two stage A bridges hold by
`rfl`. Stage B rests on `g32rep_form_preserved`: a form `E` with `contract p ∘ E = -1` for a
2-vector `p` is preserved by every injective `f` with `⋀² f p = p`.
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

variable {A : g32t_Sixfold}

theorem g32rep_mult_eq_aux (X : g32p_Cover A) (τ : FDRep ℂ g32p_G) :
    g32c_mult X τ = rfd_mult τ (g32rep_rep X) :=
  rfl

theorem g32rep_char_eq_aux (X : g32p_Cover A) (τ : FDRep ℂ g32p_G)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) :
    g32c_char X τ u hu = rfd_det τ (g32rep_rep X) u (g32rep_U_le X hu) :=
  rfl

/-- A bilinear form `E` inverse, up to sign, to the contraction of a 2-vector `p` is preserved by
every injective `f` fixing `p`: `contract (⋀² f p) = f ∘ contract p ∘ fᵀ` and `contract p` is
injective.
Source: Bourbaki, *Algèbre*, ch. IX, §1 (the form induced on the dual);
`Symplectic.contract_map`. -/
theorem g32rep_form_preserved {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (p : ⋀[ℂ]^2 W) (E : LinearMap.BilinForm ℂ W)
    (hE : ∀ x, Symplectic.contract p (E x) = -x) (f : Module.End ℂ W)
    (hf : Function.Injective f) (hfp : exteriorPower.map 2 f p = p) (x y : W) :
    E (f x) (f y) = E x y := by
  have hEinj : Function.Injective E := fun a b h => by
    have := congrArg (Symplectic.contract p) h
    rwa [hE, hE, neg_inj] at this
  have hEsurj : Function.Surjective E :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℂ) (V := W)).symm).mp hEinj
  have hCinj : Function.Injective (Symplectic.contract p) := by
    intro φ ψ h
    obtain ⟨a, rfl⟩ := hEsurj φ
    obtain ⟨b, rfl⟩ := hEsurj ψ
    rw [hE, hE, neg_inj] at h
    rw [h]
  have key : Symplectic.contract p (f.dualMap (E (f x))) = Symplectic.contract p (E x) := by
    apply hf
    have h1 := LinearMap.congr_fun (Symplectic.contract_map f p) (E (f x))
    rw [hfp, LinearMap.comp_apply, LinearMap.comp_apply] at h1
    rw [← h1, hE, hE, map_neg]
  have h2 := LinearMap.congr_fun (hCinj key) y
  rwa [LinearMap.dualMap_apply] at h2

/-- The complexified pullback of `aut g` fixes the complexified polarization 2-vector.
Source: `X.pol_inv`, `spec_homPullback_eq_cupWedgeEquiv`, `complexifyWedge_exteriorPower_map`. -/
theorem g32rep_map_polarizationVec (X : g32p_Cover A) (g : g32p_G) :
    exteriorPower.map 2 (g32rep_rep X g) (HodgeBlocks.complexifyWedge 2
      (polarizationVec (torusCohomology_cupProductOf X.J) X.pol)) =
      HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf X.J) X.pol) := by
  have h := X.pol_inv g
  rw [spec_homPullback_eq_cupWedgeEquiv] at h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  have h' := congrArg ((torusCohomology_cupProductOf X.J).cupWedgeEquiv 2).symm h
  rw [LinearEquiv.symm_apply_apply] at h'
  change exteriorPower.map 2 ((homPullback (X.aut g) 1).baseChange ℂ) _ = _
  rw [← HodgeBlocks.complexifyWedge_exteriorPower_map, polarizationVec, h']

theorem g32rep_form_spec_aux (X : g32p_Cover A) :
    (g32rep_form X).Nondegenerate ∧ (g32rep_form X).IsAlt ∧
      (∀ g x y, g32rep_form X (g32rep_rep X g x) (g32rep_rep X g y) = g32rep_form X x y) ∧
      ∀ u ∈ g32c_U X, ∀ x y, g32rep_form X (u x) (u y) = g32rep_form X x y := by
  have := (torusCohomology_cupProductOf X.J).finite
  have hE : ∀ x, Symplectic.contract (HodgeBlocks.complexifyWedge 2
      (polarizationVec (torusCohomology_cupProductOf X.J) X.pol)) (g32rep_form X x) = -x :=
    Adapters.f1575_contract_complex_dualForm X.pol_nondeg
  have halt : (g32rep_form X).IsAlt := fun x => by
    have h := Symplectic.apply_contract_self (HodgeBlocks.complexifyWedge 2
      (polarizationVec (torusCohomology_cupProductOf X.J) X.pol)) (g32rep_form X x)
    rwa [hE, map_neg, neg_eq_zero] at h
  have hleft : ∀ x, (∀ y, g32rep_form X x y = 0) → x = 0 := fun x hx => by
    have h0 : g32rep_form X x = 0 := LinearMap.ext hx
    have h := hE x
    rwa [h0, map_zero, eq_comm, neg_eq_zero] at h
  refine ⟨⟨hleft, fun y hy => hleft y fun x => halt.isRefl _ _ (hy x)⟩, halt, ?_, ?_⟩
  · intro g x y
    exact g32rep_form_preserved _ _ hE _
      ((Module.End.isUnit_iff _).1 ((Group.isUnit g).map (g32rep_rep X))).1
      (g32rep_map_polarizationVec X g) x y
  · intro u hu x y
    exact g32rep_form_preserved _ _ hE u ((Module.End.isUnit_iff u).1 hu.1).1 hu.2.2 x y

theorem g32rep_mult_eq_bot_aux (X : g32p_Cover A) (σ : FDRep ℂ g32p_G) (hσ : Simple σ)
    (hnt : ∃ g, σ.ρ g ≠ 1) (hcw : g32p_cwMult σ ≤ 0) :
    g32c_mult X σ = ⊥ := by
  have := (torusCohomology_cupProductOf X.J).finite
  rw [g32rep_mult_eq_aux]
  refine rfd_mult_eq_bot σ (g32rep_rep X) (g32p_cwMult σ) ?_ hcw
  rw [← X.mult σ hσ hnt, g32p_multiplicity]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  change LinearMap.trace ℂ _ ((homPullback (X.aut g) 1).baseChange ℂ) * _ = _
  rw [LinearMap.trace_baseChange, eq_ratCast]

theorem g32rep_quaternionic_indicator_aux (θ : FDRep ℂ g32p_G) (h : g32p_Quaternionic θ) :
    rfd_indicator θ = -1 := by
  have hc : (Fintype.card g32p_G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [rfd_indicator, h.2, mul_neg, inv_mul_cancel₀ hc]

theorem g32rep_parity_aux (X : g32p_Cover A) (θ : FDRep ℂ g32p_G) (hθ : Simple θ)
    (h : g32p_Quaternionic θ) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) :
    g32c_char X θ u hu ^ 2 = 1 := by
  have := (torusCohomology_cupProductOf X.J).finite
  obtain ⟨hnd, -, hG, hU⟩ := g32rep_form_spec_aux X
  rw [g32rep_char_eq_aux, sq]
  exact rfd_det_mul_dual (g32rep_rep X) (g32rep_form X) hnd hG θ θ hθ (fun g => (h.1 g).symm) u
    _ (hU u hu)

theorem g32rep_conj_aux (X : g32p_Cover A) {I K : Type*} (τ τbar : I → FDRep ℂ g32p_G)
    (θ : K → FDRep ℂ g32p_G) (hE : g32c_Enumeration τ τbar θ) (j : I)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) :
    g32c_char X (τbar j) u hu * g32c_char X (τ j) u hu = 1 := by
  have := (torusCohomology_cupProductOf X.J).finite
  obtain ⟨hnd, -, hG, hU⟩ := g32rep_form_spec_aux X
  rw [g32rep_char_eq_aux, g32rep_char_eq_aux]
  exact rfd_det_mul_dual (g32rep_rep X) (g32rep_form X) hnd hG (τ j) (τbar j) (hE.1 j).1
    (hE.1 j).2.2.2.1 u _ (hU u hu)

theorem g32rep_orthogonal_aux (X : g32p_Cover A) (σ : FDRep ℂ g32p_G) (hσ : Simple σ)
    (hsd : g32p_SelfDual σ) (hq : ¬ g32p_Quaternionic σ)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) :
    g32c_char X σ u hu = 1 := by
  have := (torusCohomology_cupProductOf X.J).finite
  obtain ⟨hnd, halt, hG, hU⟩ := g32rep_form_spec_aux X
  have hν : rfd_indicator σ = 1 := by
    obtain ⟨h3, h0⟩ := rfd_indicator_trichotomy σ hσ
    rcases h3 with h | h | h
    · exact h
    · exact absurd hsd (h0.1 h)
    · refine absurd ⟨hsd, ?_⟩ hq
      have hc : (Fintype.card g32p_G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
      rw [rfd_indicator, inv_mul_eq_iff_eq_mul₀ hc] at h
      rw [h, mul_neg_one]
  rw [g32rep_char_eq_aux]
  exact rfd_det_orthogonal (g32rep_rep X) (g32rep_form X) hnd halt hG σ hσ hν u _ (hU u hu)

end HodgeLean.Foundations.Program
