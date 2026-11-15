import HodgeLean.Foundations.Program.PeriodFibreMarkingProofs

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

/-- The rational comparison complexifies to the stage-one comparison.
Source: `b2b_flat`, `b2bpol_musical`; Birkenhake–Lange, §1.2. -/
theorem b64e_model_rational_complexification (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (c : ℂ) (l : Λ) :
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  (b64e_model_rational Λ F hF Q hQ).toLinearMap.baseChange ℂ
    (c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] l)) =
      b64d_model_homologyCohomology Λ F hF Q hQ (c ⊗ₜ[ℤ] l) :=
  b64e_model_rational_complexification_aux Λ F hF Q hQ c l

example := @b64e_model_rational_complexification

/-- The fibre comparison uses the inverse rational marking after scalar extension.
Source: Bourbaki, Algèbre, ch. II, §5; `LinearEquiv.baseChange`. -/
theorem b64e_fibre_marking_complexification (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (t : b6t_polydisc mr_base) (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain) (x : ℂ ⊗[ℤ] b60_Lattice) :
  (b64e_fibre_marking R m t hm).toLinearMap.baseChange ℂ
    (b60b_homologyCohomologyEquiv ⟨b64i_period R b63gP_s₀ m t.val, hm⟩ x) =
    b64e_retained_complex R t ((b64b_complexMarking _ m).symm x) :=
  b64e_fibre_marking_complexification_aux R m t hm x

example := @b64e_fibre_marking_complexification

/-- The retained and universal Weil actions intertwine.
Source: `b64d_model_homologyCohomology_intertwines`, `b63g2_operator`; Birkenhake–Lange, §1.2. -/
theorem b64e_fibre_marking_action (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y)
    (t : b6t_polydisc mr_base) (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain) :
  ∀ x, (b64e_fibre_marking R m t hm) ((b60b_univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩).W.J x) = ((b63gR_family R).fiber t).W.J ((b64e_fibre_marking R m t hm) x) :=
  b64e_fibre_marking_action_aux R m hJ hpair t hm

example := @b64e_fibre_marking_action

/-- The comparison preserves the degree-one holomorphic filtration.
Source: `b64i_chart`, `b5_period_filtration`, `b64d_model_homologyCohomology_F`. -/
theorem b64e_fibre_marking_filtration (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y)
    (t : b6t_polydisc mr_base) (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain) :
  (b60c_F (b60b_univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩)).map ((b64e_fibre_marking R m t hm).toLinearMap.baseChange ℂ) = b60c_F ((b63gR_family R).fiber t) :=
  b64e_fibre_marking_filtration_aux R m hJ hpair t hm

example := @b64e_fibre_marking_filtration

/-- The comparison carries the original polarization without a scalar factor.
Source: `b5_polarization_normalized`, `b60b_polarization_transport`; Birkenhake–Lange, §§4.1–4.3. -/
theorem b64e_fibre_marking_polarization (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y)
    (t : b6t_polydisc mr_base) (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain) :
  exteriorPower.map 2 (b64e_fibre_marking R m t hm).toLinearMap
    (polarizationVec (torusCohomology_cupProductOf (b60b_univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩).X) (b60b_univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩).pol) =
      polarizationVec (torusCohomology_cupProductOf ((b63gR_family R).fiber t).X) ((b63gR_family R).fiber t).pol :=
  b64e_fibre_marking_polarization_aux R m hJ hpair t hm

example := @b64e_fibre_marking_polarization

/-- Uniformization supplies the retained-fibre isogeny with positive multiplier.
Source: `b60c_uniformization`; Birkenhake–Lange, §1.2. -/
theorem b64e_kIsog (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y)
    (t : b6t_polydisc mr_base) (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain) :
  g32t_KIsog ((b63gR_family R).fiber t) (b60b_univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩) :=
  b64e_kIsog_aux R m hJ hpair t hm

example := @b64e_kIsog

/-- The isogenies supply the exact retained period-map input.
Source: `b63gR_periodMap`, `b60c_uniformization`; G32 v0.16, §3.3. -/
theorem b64e_hisog (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y)
    (Fm : g32m_UniversalFamily) (hFm : Fm.univ = b60b_univ) :
  ∀ (t : b6t_polydisc mr_base)
    (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain),
    g32t_KIsog ((b63gR_family R).fiber t) (Fm.univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩) :=
  b64e_hisog_aux R m hJ hpair Fm hFm

example := @b64e_hisog

/-- Interface check with the three named comparison identities. -/
example (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y)
    (t : b6t_polydisc mr_base) (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain) :=
  b60c_uniformization ((b63gR_family R).fiber t)
    ⟨b64i_period R b63gP_s₀ m t.val, hm⟩ (b64e_fibre_marking R m t hm)
    (b64e_fibre_marking_action R m hJ hpair t hm)
    (b64e_fibre_marking_filtration R m hJ hpair t hm)
    (b64e_fibre_marking_polarization R m hJ hpair t hm)

/-- The exact `hisog` binder of the retained period-map constructor. -/
example (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y)
    (Fm : g32m_UniversalFamily) (hFm : Fm.univ = b60b_univ) :
    ∀ (t : b6t_polydisc mr_base)
      (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain),
      g32t_KIsog (b63g5_fiber mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk
        R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP b63gP_s₀ (b63gR_basis R) t)
        (Fm.univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩) :=
  b64e_hisog R m hJ hpair Fm hFm

end HodgeLean.Foundations.Program
