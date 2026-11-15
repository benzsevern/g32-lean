import HodgeLean.Foundations.Program.G32RepTransport

/-! # Bodies for the restored supplier character

The body of `g32c_supplier_character`: the determinant conjunct is `g32rep_det_restrict`; the
action on `cyc_line e t` is the determinant of the transport on `V_t`, which `proj^*` identifies
with the determinant of `u` on the `χc^k`-eigenspace of `H′` (`g32rep_proj_eigen`,
`g32rep_restrict_proj`), and that is `charOf(a(χc^k))` (`g32rep_det_eigen_charOf`).
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

variable {A : g32t_Sixfold}

/-- On `V_t`, the transport of `u ∈ U` has determinant `charOf(a(χc^k))`. -/
theorem g32rep_det_restrict_eigen (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) (χc : S.H →* ℂˣ)
    (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)
    {I K : Type*} [Fintype I] [Fintype K] (τ τbar : I → FDRep ℂ g32p_G)
    (θ : K → FDRep ℂ g32p_G) (hE : g32c_Enumeration τ τbar θ)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X)
    (k : ℤ) (t : cyc_Field S.m →ₐ[ℚ] ℂ) (ht : t (g32p_zeta S) = g32p_root S.m ^ k) :
    LinearMap.det ((g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u).restrict
        (g32rep_restrict_mem_eigen X S hS hu t)) =
      g32c_charOf X τ θ u hu (papersA τ τbar θ S.H (χc ^ k)) := by
  let := (torusCohomology_cupProductOf (X.part S hS).P).finite
  set R := g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u
  rw [← g32rep_det_eigen_charOf X τ τbar θ hE S.H (χc ^ k) u hu]
  set Pc := (homPullback (X.part S hS).proj 1).baseChange ℂ
  let E : cyc_eigenspace (X.part S hS).act.cyc_coordinates t ≃ₗ[ℂ]
      rfd_eigen (g32rep_rep X) S.H (χc ^ k) :=
    (Submodule.equivMapOfInjective Pc (g32rep_proj_injective X S hS) _).trans
      (LinearEquiv.ofEq _ _ (g32rep_proj_eigen_aux X S hS χc hχc k t ht))
  have hconj : rfd_eigenAct (g32rep_rep X) S.H (χc ^ k) u (g32rep_U_le X hu) =
      (E : _ →ₗ[ℂ] _) ∘ₗ R.restrict (g32rep_restrict_mem_eigen X S hS hu t) ∘ₗ
        (E.symm : _ →ₗ[ℂ] _) := by
    refine LinearMap.ext fun w => ?_
    obtain ⟨y, rfl⟩ := E.surjective w
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    change u (Pc y) = Pc (R y)
    exact (LinearMap.congr_fun (g32rep_restrict_proj_aux X S hS hu) y).symm
  rw [hconj, LinearMap.det_conj]

theorem g32c_supplier_character_aux (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) (χc : S.H →* ℂˣ)
    (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)
    {I K : Type*} [Fintype I] [Fintype K] (τ τbar : I → FDRep ℂ g32p_G)
    (θ : K → FDRep ℂ g32p_G) (hE : g32c_Enumeration τ τbar θ)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X)
    (k : ℤ) (t : cyc_Field S.m →ₐ[ℚ] ℂ) (ht : t (g32p_zeta S) = g32p_root S.m ^ k) :
    LinearMap.det (g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u) = 1 ∧
    ∀ z ∈ cyc_line (X.part S hS).act.cyc_coordinates t,
      exteriorPower.map (2 * (X.part S hS).k)
          (g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u) z =
        g32c_charOf X τ θ u hu (papersA τ τbar θ S.H (χc ^ k)) • z := by
  refine ⟨g32rep_det_restrict_aux X S hS hu, ?_⟩
  let := (torusCohomology_cupProductOf (X.part S hS).P).finite
  have hRV := g32rep_restrict_mem_eigen X S hS hu t
  have hcomp : g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u ∘ₗ
      (cyc_eigenspace (X.part S hS).act.cyc_coordinates t).subtype =
      (cyc_eigenspace (X.part S hS).act.cyc_coordinates t).subtype ∘ₗ
        (g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u).restrict hRV :=
    rfl
  rintro z ⟨w, rfl⟩
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hcomp,
    exteriorPower.map_comp, LinearMap.comp_apply,
    rfd_exteriorPower_map_top (g32rep_finrank_eigenspace _ t), map_smul,
    g32rep_det_restrict_eigen X S hS χc hχc τ τbar θ hE u hu k t ht]

end HodgeLean.Foundations.Program
