import HodgeLean.Foundations.Program.G32Native.WeilRiemannCohomology

/-! Integral markings, the dual quadratic action and the Hodge plane. -/
noncomputable section
set_option maxRecDepth 8000
set_option maxHeartbeats 200000
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
/-- The retained integral marking with the geometric fibre as its explicit codomain.
Source: Birkenhake–Lange, Theorem 4.5.1 and §1.2. -/
def weil_marked_integralMarking : Λ ≃+ b2_abelianLattice (P).X :=
  b5_periodEquiv Λ F hF E hE

local notation "e" => weil_marked_integralMarking Λ F hF E hE J hJ hJF
local notation "Q" => b4b_transportForm Λ (g32t_Sixfold.X (weil_marked_torus Λ F hF E hE J hJ hJF)) (weil_marked_integralMarking Λ F hF E hE J hJ hJF) E
variable (hskew : ∀ x y, E (J x) y = -E x (J y))

/-- Transport through the retained integral marking and original Riemann form.
Source: Birkenhake–Lange, §§1.2–1.3, 2.2, 9.4–9.6. -/
theorem weil_marked_form_riemann  :
    b2_IsRiemannForm (b2_abelianLattice ((P).X)) (b2_abelianF ((P).X))
      (Q) := by
  apply b4b_transportForm_riemann_aux Λ ((P).X) (e)
    (F)
  · exact b5_period_filtration _ _ (hF) _
      hE
  · exact hE

/-- Transport through the retained integral marking and original Riemann form.
Source: Birkenhake–Lange, §§1.2–1.3, 2.2, 9.4–9.6. -/
theorem weil_marked_latticeClass_nondegenerate  :
    IsNondegenerate (latticeClass (b2_bilinToAddHom (Q))) := by
  obtain ⟨H, hH, hE⟩ := (b2_abelian_isRiemannForm_iff ((P).X)
    (Q)).1 (weil_marked_form_riemann Λ F hF E hE J hJ hJF)
  exact latticeClassHQ_latticeClass_nondegenerate
    (abelianPeriodLattice ((P).X)) H hH _ hE

/-- Transport through the retained integral marking and original Riemann form.
Source: Birkenhake–Lange, §§1.2–1.3, 2.2, 9.4–9.6. -/
theorem weil_marked_marking_F  :
    (F).map (b2_cplxMap (e).toAddMonoidHom) =
      b2_abelianF ((P).X) := by
  exact b5_period_filtration _ _ (hF) _
    hE

/-- Transport through the retained integral marking and original Riemann form.
Source: Birkenhake–Lange, §§1.2–1.3, 2.2, 9.4–9.6. -/
noncomputable def weil_marked_homologyCohomologyEquiv  :
    TensorProduct ℤ ℂ Λ ≃ₗ[ℂ]
      TensorProduct ℚ ℂ (HQ ((P).X) 1) :=
  let em := LinearEquiv.baseChange ℤ ℂ _ _ (e).toIntLinearEquiv
  let hflat := b2bpol_flat_bijective (b2_abelianLattice ((P).X)) (Q)
    (fun u hu ↦ b2_riemannForm_nondegenerate (b2_abelianF ((P).X))
      (Q) (b2_abelianF_isWeightOne ((P).X))
      (weil_marked_form_riemann Λ F hF E hE J hJ hJF) u hu)
  let emus := LinearEquiv.ofBijective
    (b2bpol_musical (b2_abelianLattice ((P).X)) (Q))
    (b2bpol_musical_bijective (b2_abelianLattice ((P).X)) (Q) hflat)
  let ep := LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv ((P).X))
  em.trans (emus.trans ep.symm)


end HodgeLean.Foundations.Program
