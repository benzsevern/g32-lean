import HodgeLean.Foundations.Program.PeriodBasisAlignmentProofs

/-! Implication from frame changes to ordered residue-matrix transport, and from retained
geometry to the selected multiplication jet comparison at the constructed marking.
The B6-5 kernel-frame and numerator identification remains a separate obligation.
HC no distance; AV milestone no distance. -/
noncomputable section
open Set Filter Topology Manifold
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- Invertible changes of each three-frame give an invertible ordered-product change.
Source: tensor products of linear equivalences; G32 v0.16, Subsection 5.5(7). -/
theorem b66e_productChange_unit (P R : Matrix (Fin 3) (Fin 3) ℂ)
    (hP : IsUnit P) (hR : IsUnit R) :
    IsUnit (b66e_productChange P R) :=
  b66e_productChange_unit_aux P R hP hR

example := @b66e_productChange_unit

/-- Entrywise holomorphic frame changes remain units near zero, including the product change.
Source: Mathlib AnalyticAt.mul; continuity of determinant and its nonzero locus. -/
theorem b66e_productChange_analytic (P R : ℂ → Matrix (Fin 3) (Fin 3) ℂ)
    (hP : ∀ i j, AnalyticAt ℂ (fun θ => P θ i j) 0)
    (hR : ∀ i j, AnalyticAt ℂ (fun θ => R θ i j) 0)
    (huP : IsUnit (P 0)) (huR : IsUnit (R 0)) :
    (∀ i j, AnalyticAt ℂ (fun θ => b66e_productChange (P θ) (R θ) i j) 0) ∧
    ∀ᶠ θ in 𝓝 (0 : ℂ), IsUnit (P θ) ∧ IsUnit (R θ) ∧
      IsUnit (b66e_productChange (P θ) (R θ)) :=
  b66e_productChange_analytic_aux P R hP hR huP huR

example := @b66e_productChange_analytic

/-- Residue multiplication changes by the ordered product of the two column changes.
Source: Forster, Lectures on Riemann Surfaces, §17, bilinearity of residue duality. -/
theorem b66e_multiplication_transport (D : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q r : Fin 3 → b66g_primitiveForms D t)
    (P R : Matrix (Fin 3) (Fin 3) ℂ)
    (S : Fin 10 → Finset D.C) (v : Fin 10 → b66k_Index D → ℂ → ℂ)
    (hmero : ∀ j a z, z ∈ b66k_domain D t a → MeromorphicAt (v j a) z) :
    b66m_multiplicationMatrix D t (b66e_reframe D t q P)
      (b66e_reframe D t r R) S v =
        b66e_productChange P R * b66m_multiplicationMatrix D t q r S v :=
  b66e_multiplication_transport_aux D t q r P R S v hmero

example := @b66e_multiplication_transport

/-- The selected geometric multiplication jet has the exact comparison at the constructed marking.
The explicit output factor retains the residue sign and graph-index reversal.
Source: b66m_jet_codiff; b63gW_marking_hJ; b63gW_marking_hpair. -/
theorem b66e_marked_codiff (D : rf8_SharedFamily)
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (curve : ℂ → Fin 10 → ℂ) (hcurve : ContinuousAt curve 0)
    (hzero : curve 0 ∈ b6t_polydisc mr_base) :
    ∃ (q r : (t : b6t_polydisc mr_base) → Fin 3 → b66g_primitiveForms D t)
      (S : (t : b6t_polydisc mr_base) → Fin 10 → Finset D.C)
      (v : (t : b6t_polydisc mr_base) → Fin 10 → b66k_Index D → ℂ → ℂ),
      (∀ t, LinearIndependent ℂ
        (fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q t ij.2 else r t ij.2)) ∧
      (∀ t j a z, z ∈ b66k_domain D t a → MeromorphicAt (v t j a) z) ∧
      (∀ t j a z, z ∈ b66k_domain D t a →
        ((D.atlas.A a).symm (t.val, z)).2 ∉ S t j → AnalyticAt ℂ (v t j a) z) ∧
      (∀ t j a b x, x ∉ S t j → (t, x) ∈ (D.atlas.A a).source →
        (t, x) ∈ (D.atlas.A b).source →
        b66k_cocycle D t (Pi.single j 1) a b x = b66k_boundary D t (v t j) a b x) ∧
      (∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
        ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
          b66m_jet D q r S v curve θ = L * LinearMap.toMatrix'
            (fderiv ℂ (b64i_period D b63gP_s₀
              (b63gW_marking D u₀ hroot)) (curve θ) :
                (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T) ∧
      (∀ᶠ θ in 𝓝 (0 : ℂ), ∃ κ : ℂ,
        (κ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ∨
          κ = -(2 * (Real.pi : ℂ) * Complex.I)⁻¹) ∧
        IsUnit (b66m_leftMatrix (b64i_period D b63gP_s₀
          (b63gW_marking D u₀ hroot) (curve θ)) κ) ∧
        b66m_jet D q r S v curve θ =
          b66m_leftMatrix (b64i_period D b63gP_s₀
            (b63gW_marking D u₀ hroot) (curve θ)) κ *
          LinearMap.toMatrix' (fderiv ℂ (b64i_period D b63gP_s₀
            (b63gW_marking D u₀ hroot)) (curve θ) :
              (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * (1 : Matrix (Fin 10) (Fin 10) ℂ)) :=
  b66e_marked_codiff_aux D u₀ hroot curve hcurve hzero

example := @b66e_marked_codiff

/-- The existing consumer field uses precisely nine output rows and ten input columns.
This check projects the field without selecting a geometric witness. -/
example (Fm : HodgeLean.Papers.g32m_UniversalFamily)
    (D : rf8_SharedFamily)
    (F : HodgeLean.Papers.g32r_PeriodMap Fm (b63gR_family D)) :
    ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        F.jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ F.period (F.curve θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T := F.codiff

end HodgeLean.Foundations.Program
