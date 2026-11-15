import HodgeLean.Foundations.Program.PathCoverFamilyWrappers
import HodgeLean.Foundations.Program.NamedLoopFamily

/-! # Selected-family route obligations
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

theorem b65z_theoremA_of_transport_selected_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    let g := Classical.choose (b65z_schlesinger_identification p hp)
    let hg := Classical.choose_spec (b65z_schlesinger_identification p hp)
    let D := Classical.choose hg.2
    let hD := Classical.choose_spec hg.2
    let e := Classical.choose hD
    let he := Classical.choose_spec hD
    let x := Classical.choose he.2
    let hx := Classical.choose_spec he.2
    let u₀ := Classical.choose hx
    let hu := Classical.choose_spec hx
    let δ := Classical.choose hu
    let hδ := Classical.choose_spec hu
    let C := Classical.choose hδ.2.2
    let hT := Classical.choose_spec hδ.2.2
    ∀
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (h46 : g32s_Prop46 P)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff :
      let m₀ := Classical.choose
        (b65z_marking_u p hp g D e he.1 x u₀ δ hδ.1 hδ.2.1 C hT)
      ∀ᶠ θ in 𝓝 (0 : ℂ),
        ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
        ∃ T : Matrix (Fin 10) (Fin 10) ℂ,
          IsUnit L ∧ IsUnit T ∧
          jet θ = L * LinearMap.toMatrix'
            (fderiv ℂ
              (b65z_period D (b65z_s₀ (b65z_centre p)) m₀)
              (b65p_curve p θ) :
                (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T)
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) , G32TheoremAStatement A W pol := by
  intro g hg D hD e he x hx u₀ hu δ hδ C hT B P hP F hF h46 jet jet_certified codiff transport A _ _ _ _ _ W pol
  exact b65z_theoremA_of_transport_certified p O D B P hP F hF h46 hp e he.1 x u₀ δ hδ.1 hδ.2.1 C hT
    jet jet_certified codiff transport A W pol

theorem b65z_theoremA_of_reverse_selected_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    let g := Classical.choose (b65z_schlesinger_identification p hp)
    let hg := Classical.choose_spec (b65z_schlesinger_identification p hp)
    let D := Classical.choose hg.2
    let hD := Classical.choose_spec hg.2
    let e := Classical.choose hD
    let he := Classical.choose_spec hD
    let x := Classical.choose he.2
    let hx := Classical.choose_spec he.2
    let u₀ := Classical.choose hx
    let hu := Classical.choose_spec hx
    let δ := Classical.choose hu
    let hδ := Classical.choose_spec hu
    let C := Classical.choose hδ.2.2
    let hT := Classical.choose_spec hδ.2.2
    ∀
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (h46 : g32s_Prop46 P)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff :
      let m₀ := Classical.choose
        (b65z_marking_u p hp g D e he.1 x u₀ δ hδ.1 hδ.2.1 C hT)
      ∀ᶠ θ in 𝓝 (0 : ℂ),
        ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
        ∃ T : Matrix (Fin 10) (Fin 10) ℂ,
          IsUnit L ∧ IsUnit T ∧
          jet θ = L * LinearMap.toMatrix'
            (fderiv ℂ
              (b65z_period D (b65z_s₀ (b65z_centre p)) m₀)
              (b65p_curve p θ) :
                (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T)
    (reverse : ∀ P Q, g32t_IsMember P → g32t_IsMember Q → g32t_KIsog P Q → g32t_KIsog Q P)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) , G32TheoremAStatement A W pol := by
  intro g hg D hD e he x hx u₀ hu δ hδ C hT B P hP F hF h46 jet jet_certified codiff reverse A _ _ _ _ _ W pol
  exact b65z_theoremA_of_reverse_certified p O D B P hP F hF h46 hp e he.1 x u₀ δ hδ.1 hδ.2.1 C hT
    jet jet_certified codiff reverse A W pol

theorem b65z_theoremA_of_qinv_selected_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    let g := Classical.choose (b65z_schlesinger_identification p hp)
    let hg := Classical.choose_spec (b65z_schlesinger_identification p hp)
    let D := Classical.choose hg.2
    let hD := Classical.choose_spec hg.2
    let e := Classical.choose hD
    let he := Classical.choose_spec hD
    let x := Classical.choose he.2
    let hx := Classical.choose_spec he.2
    let u₀ := Classical.choose hx
    let hu := Classical.choose_spec hx
    let δ := Classical.choose hu
    let hδ := Classical.choose_spec hu
    let C := Classical.choose hδ.2.2
    let hT := Classical.choose_spec hδ.2.2
    ∀
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (h46 : g32s_Prop46 P)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff :
      let m₀ := Classical.choose
        (b65z_marking_u p hp g D e he.1 x u₀ δ hδ.1 hδ.2.1 C hT)
      ∀ᶠ θ in 𝓝 (0 : ℂ),
        ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
        ∃ T : Matrix (Fin 10) (Fin 10) ℂ,
          IsUnit L ∧ IsUnit T ∧
          jet θ = L * LinearMap.toMatrix'
            (fderiv ℂ
              (b65z_period D (b65z_s₀ (b65z_centre p)) m₀)
              (b65p_curve p θ) :
                (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T)
    (qinv : qinv_premise)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) , G32TheoremAStatement A W pol := by
  intro g hg D hD e he x hx u₀ hu δ hδ C hT B P hP F hF h46 jet jet_certified codiff qinv A _ _ _ _ _ W pol
  exact b65z_theoremA_of_qinv_certified p O D B P hP F hF h46 hp e he.1 x u₀ δ hδ.1 hδ.2.1 C hT
    jet jet_certified codiff qinv A W pol

end HodgeLean.Foundations.Program
