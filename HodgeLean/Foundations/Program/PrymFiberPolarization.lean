import HodgeLean.Foundations.Program.PrymFiberPolarizationProofs

/-! # Polarizations of retained Prym fibres
Implication from shared geometry and based root monodromy to singular and model
discriminants and parabolic polarizations at every parameter.
HC no distance; AV milestone no distance.
-/
noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open HodgeLean.Foundations.WeilHermitian HodgeLean.Foundations.HermitianForm
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- B5 transport to the model polarization with positive scale one.
Source: `b63f_polarization`, `b63f_fibre_comparison`, `b63g4_polarizationForm_column`; Birkenhake–Lange, §§4.1–4.2. -/
theorem b63hp_normalization (D : rf8_SharedFamily) (s : b6t_polydisc mr_base) :
    let Λ := b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) s
    let E := b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) s (D.P s) (D.Q s)
    let X := ((b63gR_family D).fiber s).X
    let h := g32h_fiber_polarized (b63gR_family D) s
    letI := (torusCohomology_cupProductOf X).finite
    ∃ e : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] HQ X 1,
      (∀ x, e ((D.A s).baseChange ℚ x) = -((b63gR_family D).fiber s).W.J (e x)) ∧
      ∃ c : ℚ, c = 1 ∧ 0 < c ∧
        ∀ x y, polarizationForm (torusCohomology_cupProductOf X) h.nondegenerate
          (e x) (e y) = c * E.baseChange ℚ x y :=
  b63hp_normalization_aux D s

example := @b63hp_normalization

/-- The singular Weil form has class [−2] at every retained parameter.
Source: `hg7g_parameter_discriminant`, `hg7g_retained_discriminant`; G32 v0.16, Proposition 6.3. -/
theorem b63hp_singular_discriminant (D : rf8_SharedFamily)
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) (s : b6t_polydisc mr_base) :
    let Λ := b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) s
    let E := b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _) s
      (D.P s) (D.Q s)
    letI : Module.Finite ℤ Λ := Module.Finite.of_basis (b63hp_basis D s)
    ∃ hJ : (D.A s).baseChange ℚ ∘ₗ (D.A s).baseChange ℚ =
        (-3 : ℚ) • LinearMap.id,
    ∃ hskew : ∀ x y, E.baseChange ℚ ((D.A s).baseChange ℚ x) y =
        -E.baseChange ℚ x ((D.A s).baseChange ℚ y),
    ∃ hh : (b64b_latticeH Λ E ⟨(D.A s).baseChange ℚ, hJ⟩ hskew).IsSymm,
    ∃ hn : (b64b_latticeH Λ E ⟨(D.A s).baseChange ℚ, hJ⟩ hskew).Nondegenerate,
      detClass (b64b_latticeH Λ E ⟨(D.A s).baseChange ℚ, hJ⟩ hskew) hh hn =
        classNegTwo :=
  b63hp_singular_discriminant_aux D u₀ hroot s

example := @b63hp_singular_discriminant

/-- The B5 model discriminant at every retained parameter.
Source: `b63hp_normalization`, `b63hp_singular_discriminant`; G32 v0.16, Proposition 6.3. -/
theorem b63hp_model_discriminant (D : rf8_SharedFamily)
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) (s : b6t_polydisc mr_base) :
    g32t_disc (g32h_fiber_polarized (b63gR_family D) s) = classNegTwo :=
  b63hp_model_discriminant_aux D u₀ hroot s

example := @b63hp_model_discriminant

/-- Parabolic polarizations of all retained fibres.
Source: `hp_parabolicPolarization_of_disc`, `b63hp_model_discriminant`; G32 v0.16, Proposition 6.3. -/
theorem b63hp_parabolicPolarization (D : rf8_SharedFamily)
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) :
    ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized (b63gR_family D) s) :=
  b63hp_parabolicPolarization_aux D u₀ hroot

example := @b63hp_parabolicPolarization

/-- The all-parameter result supplies the fibre polarization binder of the retained route. -/
example (D : rf8_SharedFamily)
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D)) 
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((D.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (D.P b63gP_s₀) (D.Q b63gP_s₀)).baseChange ℚ x y)
    (curve : ℂ → Fin 10 → ℂ) (curve_cont : ContinuousAt curve 0)
    (curve_zero : curve 0 ∈ b6t_polydisc mr_base)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b64i_period D b63gP_s₀ m) (curve θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T)
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gU_theoremA_of_transport D F hF h46 m hJ hpair curve curve_cont
    curve_zero jet jet_certified codiff (b63hp_parabolicPolarization D u₀ hroot) transport A W pol

end HodgeLean.Foundations.Program
