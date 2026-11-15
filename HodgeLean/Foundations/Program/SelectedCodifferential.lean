import HodgeLean.Foundations.Program.SelectedCodifferentialProofs

/-! # Numerator comparison at the selected marking

Implication from root-box data and deformation outputs to pointwise matrix equivalence
at the marking selected by `b65z_marking_u`. The three routes retain the local Prym
package, universal family, Proposition 4.6 and their route premise. No analytic
dependence of matrix changes or additional geometric realization is asserted.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option linter.unusedVariables false
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

/-- The numerator comparison at the actual selected marking.
Source: b66f_numerator_codiff, b66d_dictionary, b65g_full_kernels,
b66d_cover_solutions_conj; G32 v0.16, Lemma 5.8. -/
theorem b66j_codiff_supplier (p : Fin 12 → ℂ) (O : b65p_Outputs p)
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
    let m₀ := Classical.choose
      (b65z_marking_u p hp g D e he.1 x u₀ δ hδ.1 hδ.2.1 C hT)
    ∀ᶠ θ in 𝓝 (0 : ℂ),
      ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ,
        IsUnit L ∧ IsUnit T ∧
        b65e_numerator p O.residue θ = L * LinearMap.toMatrix'
          (fderiv ℂ
            (b65z_period D (b65z_s₀ (b65z_centre p)) m₀)
            (b65p_curve p θ) :
              (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T :=
  b66j_codiff_supplier_aux p O hp

example := @b66j_codiff_supplier

/-- Certification of the numerator array used in the selected routes.
Source: NumeratorJet.lean, b65e_certified. -/
theorem b66j_jet_certified (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    g32r_CertifiedJet (b65e_numerator p O.residue) :=
  b66j_jet_certified_aux p O

example := @b66j_jet_certified

/-- The selected transport route using the numerator supplier.
Source: b65z_theoremA_of_transport_selected, b66j_codiff_supplier,
b65e_certified; G32 v0.16, Theorem A. -/
theorem b65z_theoremA_of_transport_codiff (p : Fin 12 → ℂ) (O : b65p_Outputs p)
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
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) , G32TheoremAStatement A W pol :=
  b65z_theoremA_of_transport_codiff_aux p O hp

example := @b65z_theoremA_of_transport_codiff

/-- The selected reverse route using the numerator supplier.
Source: b65z_theoremA_of_reverse_selected, b66j_codiff_supplier,
b65e_certified; G32 v0.16, Theorem A. -/
theorem b65z_theoremA_of_reverse_codiff (p : Fin 12 → ℂ) (O : b65p_Outputs p)
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
    (reverse : ∀ P Q, g32t_IsMember P → g32t_IsMember Q → g32t_KIsog P Q → g32t_KIsog Q P)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) , G32TheoremAStatement A W pol :=
  b65z_theoremA_of_reverse_codiff_aux p O hp

example := @b65z_theoremA_of_reverse_codiff

/-- The selected qinv route using the numerator supplier.
Source: b65z_theoremA_of_qinv_selected, b66j_codiff_supplier,
b65e_certified; G32 v0.16, Theorem A. -/
theorem b65z_theoremA_of_qinv_codiff (p : Fin 12 → ℂ) (O : b65p_Outputs p)
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
    (qinv : qinv_premise)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) , G32TheoremAStatement A W pol :=
  b65z_theoremA_of_qinv_codiff_aux p O hp

example := @b65z_theoremA_of_qinv_codiff

/-- Interface check against the selected qinv wrapper's literal comparison argument.
This uses the open supplier solely to check the consumer type. -/
example (p : Fin 12 → ℂ) (O : b65p_Outputs p)
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
    (qinv : qinv_premise)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) , G32TheoremAStatement A W pol := by
  intro g hg D hD e he x hx u₀ hu δ hδ C hT B P hP F hF h46 qinv A _ _ _ _ _ W pol
  exact b65z_theoremA_of_qinv_selected p O hp B P hP F hF h46
    (b65e_numerator p O.residue) (b65e_certified p O)
    (b66j_codiff_supplier p O hp) qinv A W pol

/-- The certified numerator has a nonzero first coefficient, independently of this stage. -/
example : b65e_N 1 ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun h 0) 0
  change (10672605 / 512 : ℚ) = 0 at hentry
  norm_num at hentry

/-- An actual residue sum is nonzero, independently of this stage. -/
example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (x : D.C) :
    b66f_residueSum D t {x} (fun _ z => (z - (D.atlas.A (t, x) (t, x)).2)⁻¹) 1 = 1 := by
  simp [b66f_residueSum]

/-- Assembly interface: the solution convention, full kernels and dictionary use the
same selected family and the marking's own two identities. This checks dependencies;
it uses the imported open dictionary and is not an independent geometric check. -/
example (p : Fin 12 → ℂ) (O : b65p_Outputs p)
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
    let m₀ := Classical.choose
      (b65z_marking_u p hp g D e he.1 x u₀ δ hδ.1 hδ.2.1 C hT)
    ∀ᶠ θ in 𝓝 (0 : ℂ),
      ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ,
        IsUnit L ∧ IsUnit T ∧
        b65e_numerator p O.residue θ = L * LinearMap.toMatrix'
          (fderiv ℂ
            (b65z_period D (b65z_s₀ (b65z_centre p)) m₀)
            (b65p_curve p θ) :
              (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T := by
  intro g hg D hD e he x hx u₀ hu δ hδ C hT m₀
  have hm := Classical.choose_spec
    (b65z_marking_u p hp g D e he.1 x u₀ δ hδ.1 hδ.2.1 C hT)
  obtain ⟨S, hconj⟩ := b66d_cover_solutions_conj p O D e he.1 x u₀ C hT
  obtain ⟨ε, hε, _, hker⟩ := b65g_full_kernels p O g hg.1 D S
  exact b66f_numerator_codiff p O hg.1 D m₀ hm.1 hm.2
    (Filter.Eventually.mono (Metric.ball_mem_nhds (0 : ℂ) hε)
      fun θ hθ => (hker θ hθ).2.2)
    (b66d_dictionary p O hg.1 D S hconj m₀ hm.1 hm.2
      (b65g_frames p O g hg.1 D S) (b65g_units p O g hg.1 D S)
      (b65g_branch_coordinates p O))

end HodgeLean.Foundations.Program
