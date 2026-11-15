import HodgeLean.Foundations.Program.G32Native.WeilMarkedRosati

/-! Rational dual marking for Hermitian determinant transport. -/
noncomputable section
set_option maxRecDepth 8000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.AppellHumbert
namespace HodgeLean.Foundations.Program
variable (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (E : LinearMap.BilinForm ℤ Λ) (hE : b2_IsRiemannForm Λ F E)
    (J : Λ →+ Λ) (hJ : ∀ x, J (J x) = (-3 : ℤ) • x)
    (hJF : F ≤ F.comap (b2_cplxMap J))
local notation "P" => weil_marked_torus Λ F hF E hE J hJ hJF
local notation "e" => weil_marked_integralMarking Λ F hF E hE J hJ hJF
local notation "Q" => b4b_transportForm Λ (g32t_Sixfold.X (weil_marked_torus Λ F hF E hE J hJ hJF)) (weil_marked_integralMarking Λ F hF E hE J hJ hJF) E
variable (hskew : ∀ x y, E (J x) y = -E x (J y))

/-- Compare the rational dual lattice with geometric cohomology through the same marking.
Source: Birkenhake–Lange, §§1.2–1.3, 9.4–9.6; van Geemen, LNM 1594, §5.4. -/
def weil_marked_markedDualEquiv  :
    b2b_dual Λ ≃ₗ[ℚ] b2b_dual (b2_abelianLattice ((P).X)) where
  toFun f := f ∘ₗ (e).symm.toIntLinearEquiv.toLinearMap
  invFun f := f ∘ₗ (e).toIntLinearEquiv.toLinearMap
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Compare the rational dual lattice with geometric cohomology through the same marking.
Source: Birkenhake–Lange, §§1.2–1.3, 9.4–9.6; van Geemen, LNM 1594, §5.4. -/
def weil_marked_cohomologyEquiv  :
    b2b_dual Λ ≃ₗ[ℚ] HQ ((P).X) 1 :=
  (weil_marked_markedDualEquiv Λ F hF E hE J hJ hJF).trans (b60b_periodLinearEquiv ((P).X)).symm

/-- Compare the rational dual lattice with geometric cohomology through the same marking.
Source: Birkenhake–Lange, §§1.2–1.3, 9.4–9.6; van Geemen, LNM 1594, §5.4. -/
theorem weil_marked_cohomologyEquiv_action  (x : b2b_dual Λ) :
    weil_marked_cohomologyEquiv Λ F hF E hE J hJ hJF (b60b_dualPrecomp J x) =
      (P).W.J (weil_marked_cohomologyEquiv Λ F hF E hE J hJ hJF x) := by
  apply (b60b_periodLinearEquiv ((P).X)).injective
  simp only [weil_marked_cohomologyEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  ext l
  change x (J ((e).symm l)) =
    abelianPeriodEquiv ((P).X)
      ((P).W.J ((b60b_periodLinearEquiv ((P).X)).symm
        (weil_marked_markedDualEquiv Λ F hF E hE J hJ hJF x))) l
  change _ = abelianPeriodEquiv (P).X (b4b_cohomologyAction Λ (P).X e J _) _
  unfold b4b_cohomologyAction
  simp [weil_marked_markedDualEquiv, b60b_periodLinearEquiv, b60b_addHomLinearEquiv, b60b_dualPrecomp,
    b4b_periodPrecomp]
  change x (J ((e).symm l)) =
    x ((e).symm (e
      (J ((e).symm l))))
  rw [(e).symm_apply_apply]

/-- Compare the rational dual lattice with geometric cohomology through the same marking.
Source: Birkenhake–Lange, §§1.2–1.3, 9.4–9.6; van Geemen, LNM 1594, §5.4. -/
theorem weil_marked_cohomologyEquiv_form  (x y : b2b_dual Λ) :
    polarizationForm (torusCohomology_cupProductOf ((P).X))
        (b2_abelian_nondegenerate ((P).X) (Q)
          (weil_marked_form_riemann Λ F hF E hE J hJ hJF))
        (weil_marked_cohomologyEquiv Λ F hF E hE J hJ hJF x) (weil_marked_cohomologyEquiv Λ F hF E hE J hJ hJF y) =
      b2b_dualForm Λ E x y := by
  rw [weil_riemann_polarizationForm_period (P).X Q (weil_marked_form_riemann Λ F hF E hE J hJ hJF)]
  have he (z : b2b_dual Λ) :
      b60b_periodLinearEquiv ((P).X) (weil_marked_cohomologyEquiv Λ F hF E hE J hJ hJF z) =
        weil_marked_markedDualEquiv Λ F hF E hE J hJ hJF z := by
    exact (b60b_periodLinearEquiv ((P).X)).apply_symm_apply _
  rw [he x, he y]
  exact b2bpol_dualForm_comp (Λ := Λ)
    (Λ' := b2_abelianLattice ((P).X)) E (Q) (e)
    (fun x y ↦ by
      change E ((e).symm ((e) x)) ((e).symm ((e) y)) = E x y
      rw [(e).symm_apply_apply, (e).symm_apply_apply]) x y


#print axioms weil_marked_cohomologyEquiv_form
#print axioms weil_marked_cohomologyEquiv_action
end HodgeLean.Foundations.Program
