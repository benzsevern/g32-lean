import HodgeLean.Foundations.Program.ComponentTransportChainRestored

/-! # Proof obligations for the G32-centre route wrappers
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

theorem b65z_theoremA_of_transport_certified_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily (b65z_centre p) g)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (h46 : g32s_Prop46 P)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (hmono : ∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff :
      let m₀ := Classical.choose
        (b65z_marking_u p hp g D e he x u₀ δ hδ hmono C hT)
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  let m₀ := Classical.choose
    (b65z_marking_u p hp g D e he x u₀ δ hδ hmono C hT)
  obtain ⟨hJ₀, hpair₀⟩ := Classical.choose_spec
    (b65z_marking_u p hp g D e he x u₀ δ hδ hmono C hT)
  obtain ⟨j, hj⟩ := hP
  have hpol := (b65z_polarization_u p hp g D e he x u₀ δ hδ hmono C hT B P j hj).2
  exact b65z_theoremA_of_transport p O D B P ⟨j, hj⟩ F hF h46
    m₀ hJ₀ hpair₀ jet jet_certified codiff hpol transport A W pol

theorem b65z_theoremA_of_reverse_certified_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily (b65z_centre p) g)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (h46 : g32s_Prop46 P)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (hmono : ∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff :
      let m₀ := Classical.choose
        (b65z_marking_u p hp g D e he x u₀ δ hδ hmono C hT)
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  let m₀ := Classical.choose
    (b65z_marking_u p hp g D e he x u₀ δ hδ hmono C hT)
  obtain ⟨hJ₀, hpair₀⟩ := Classical.choose_spec
    (b65z_marking_u p hp g D e he x u₀ δ hδ hmono C hT)
  obtain ⟨j, hj⟩ := hP
  have hpol := (b65z_polarization_u p hp g D e he x u₀ δ hδ hmono C hT B P j hj).2
  exact b65z_theoremA_of_reverse p O D B P ⟨j, hj⟩ F hF h46
    m₀ hJ₀ hpair₀ jet jet_certified codiff hpol reverse A W pol

theorem b65z_theoremA_of_qinv_certified_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily (b65z_centre p) g)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (h46 : g32s_Prop46 P)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (hmono : ∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff :
      let m₀ := Classical.choose
        (b65z_marking_u p hp g D e he x u₀ δ hδ hmono C hT)
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  let m₀ := Classical.choose
    (b65z_marking_u p hp g D e he x u₀ δ hδ hmono C hT)
  obtain ⟨hJ₀, hpair₀⟩ := Classical.choose_spec
    (b65z_marking_u p hp g D e he x u₀ δ hδ hmono C hT)
  obtain ⟨j, hj⟩ := hP
  have hpol := (b65z_polarization_u p hp g D e he x u₀ δ hδ hmono C hT B P j hj).2
  exact b65z_theoremA_of_qinv p O D B P ⟨j, hj⟩ F hF h46
    m₀ hJ₀ hpair₀ jet jet_certified codiff hpol qinv A W pol

end HodgeLean.Foundations.Program
