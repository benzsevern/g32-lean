import HodgeLean.Foundations.Program.PeriodComparisonModel
import HodgeLean.Foundations.Program.PrymFamilyShared

/-! # Rational comparison and retained fibre marking
Implication from integral Riemann data and a rational marking to fibre comparisons.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry Set Manifold HodgeLean.Papers
open HodgeLean.RealDefs HodgeLean.Adapters
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- Rational row comparison for a B5 model with the original form.
Source: Birkenhake–Lange, §§1.2–1.3; `b2b_flat`, `b5_periodEquiv`. -/
def b64e_model_rational (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  ℚ ⊗[ℤ] Λ ≃ₗ[ℚ] HQ (b5_model Λ F hF Q) 1 :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  let X := b5_model Λ F hF Q
  let e := b5_periodEquiv Λ F hF Q hQ
  let R := b4b_transportForm Λ X e Q
  let hR := b4b_transportForm_riemann_aux Λ X e F
    (b5_period_filtration Λ F hF Q hQ) Q hQ
  let flat := LinearEquiv.ofBijective (b2b_flat (b2_abelianLattice X) R)
    (b2bpol_flat_bijective (b2_abelianLattice X) R
      (fun u hu ↦ b2_riemannForm_nondegenerate (b2_abelianF X) R
        (b2_abelianF_isWeightOne X) hR u hu))
  (LinearEquiv.baseChange ℤ ℚ _ _ e.toIntLinearEquiv).trans
    (flat.trans (b60b_periodLinearEquiv X).symm)

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  Function.Bijective (b64e_model_rational Λ F hF Q hQ) :=
  (b64e_model_rational Λ F hF Q hQ).bijective

/-- Rational comparison on the exact retained B5 fibre, using its transported filtration.
Source: `b63g5_fiber`, `b63e_weight_one_riemann`; Birkenhake–Lange, §12.2. -/
def b64e_retained_rational (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀ ≃ₗ[ℚ] HQ ((b63gR_family R).fiber t).X 1 := by
  letI := Module.Free.of_basis (b63gR_basis R)
  letI := Module.Finite.of_basis (b63gR_basis R)
  exact b64e_model_rational _ _
    (b63e_weight_one_riemann mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
      R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk
      R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP b63gP_s₀ t).1 _
    (b63e_weight_one_riemann mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
      R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk
      R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP b63gP_s₀ t).2


/-- Complex comparison on the exact retained B5 fibre, using its transported filtration.
Source: `b63g5_fiber`, `b63e_weight_one_riemann`; Birkenhake–Lange, §12.2. -/
def b64e_retained_complex (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ℂ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀ ≃ₗ[ℂ] ℂ ⊗[ℚ] HQ ((b63gR_family R).fiber t).X 1 := by
  letI := Module.Free.of_basis (b63gR_basis R)
  letI := Module.Finite.of_basis (b63gR_basis R)
  exact b64d_model_homologyCohomology _ _
    (b63e_weight_one_riemann mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
      R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk
      R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP b63gP_s₀ t).1 _
    (b63e_weight_one_riemann mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
      R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk
      R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP b63gP_s₀ t).2


example := @b64e_retained_complex

example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Function.Bijective (b64e_retained_rational R t) := (b64e_retained_rational R t).bijective

/-- Marking from universal cohomology to retained fibre cohomology.
Source: `b64e_model_rational`, `b64e_retained_rational`; Birkenhake–Lange, §1.2. -/
def b64e_fibre_marking (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (t : b6t_polydisc mr_base) (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain) :
    HQ (b60b_univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩).X 1 ≃ₗ[ℚ]
      HQ ((b63gR_family R).fiber t).X 1 :=
  (b64e_model_rational b60_Lattice _ (b60_weight_one ⟨_, hm⟩)
    b60_E ((b60_riemann_iff _).2 hm)).symm.trans
      (m.symm.trans (b64e_retained_rational R t))

example := @b64e_fibre_marking

example (R : rf8_SharedFamily) : Module.finrank ℤ
    (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) = 12 := by
  rw [Module.finrank_eq_card_basis (b63gR_basis R), Fintype.card_fin]

example (R : rf8_SharedFamily) (t : (b63gR_family R).S) :
    g32h_h10 ((b63gR_family R).fiber t) = 3 ∧
      g32h_h01 ((b63gR_family R).fiber t) = 3 := g32h_h10_eq_three _ t

example : Nonempty rf8_SharedFamily := by
  obtain ⟨R, _⟩ := rf8_shared_root
  exact ⟨R⟩

/-- Positive rank and nontrivial monodromy checks use existing bodies. -/
example (R : rf8_SharedFamily) (t : (b63gR_family R).S) (i : Fin 13) :
    (b63gR_family R).tuple t i ≠ 1 := by
  intro hi
  change b63g5_tuple i = 1 at hi
  have h1 : b4b_root i = 1 :=
    Subtype.val_injective (hi.trans (map_one b4b_toMatrix).symm)
  have h3 := b63_root_order i
  rw [h1, orderOf_one] at h3
  split_ifs at h3 <;> omega

end HodgeLean.Foundations.Program
