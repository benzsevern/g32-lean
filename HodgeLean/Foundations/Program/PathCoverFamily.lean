import HodgeLean.Foundations.Program.PathCoverFamilyProofs

/-! # B6-5: the retained cover family along the G32 Schlesinger path

Implication from a supplied retained family and a compatible rational marking to the local
period function, holomorphic with values in `𝓗₃` and with fibre isogenies; implication to the
Prym family of the retained fibres; and Theorem A along the G32 path on the three existing
routes, as lower-level implications that keep the marking and the polarization as binders,
with the local family in place of `mr_base`. Family existence, certified identification,
marking and polarization suppliers are set aside in `docs/specs/PathCoverFamily.md`.

Not claimed: Proposition 4.6, the certified jet, the codifferential comparison or any route input
(all binders); the premise-removing route wrappers (planned in `docs/specs/PathCoverFamily.md`);
the analytic continuation of the `mr_base` family to the G32 centre; any statement about `θ ≠ 0`
beyond the curve fields of the 5c record.
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

/-- **The local period function.** For a retained family about any centre `c` with a tuple in
the G32 Nielsen class and a rational marking of the reference lattice compatible with `1 + 2ω` and
the polarization, the period coordinate function is holomorphic on the polydisc, takes values in
`g32m_Domain` and represents the transported filtration there, and every retained fibre is
`K`-isogenous to the universal fibre at its period. This generalizes `b64i_analytic`,
`b64i_chart` and `b64e_kIsog` from `mr_base` to `c`.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, §1 and §2; G32 v0.16, §2.2
(lem:isogeny), §3.3 and Lemma 3.6; `b64i_analytic`, `b64i_chart`, `b64e_kIsog`,
`b60c_uniformization`. -/
theorem b65z_local_period (c : Fin 10 → ℂ) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ c)).baseChange ℚ y) = b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)
        (D.P (b65z_s₀ c)) (D.Q (b65z_s₀ c))).baseChange ℚ y z) :
    AnalyticOnNhd ℂ (b65z_period D (b65z_s₀ c) m) (b6t_polydisc c) ∧
    (∀ t ∈ b6t_polydisc c, b65z_period D (b65z_s₀ c) m t ∈ g32m_Domain ∧
      b60_F (b65z_period D (b65z_s₀ c) m t) =
        b64c_markedF _ m (b65z_transportedFamily D (b65z_s₀ c)) t) ∧
    ∀ (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c))) (t : b6t_polydisc c)
      (hm : b65z_period D (b65z_s₀ c) m t.val ∈ g32m_Domain),
      g32t_KIsog (b65z_fiber D B t) (b60b_univ ⟨b65z_period D (b65z_s₀ c) m t.val, hm⟩) :=
  b65z_local_period_aux c g hg D m hJ hpair

example := @b65z_local_period

/-- **The Prym family of the retained fibres about `c`.** For a retained family about any centre
with a tuple in the G32 Nielsen class, the reference lattice has a basis of rank twelve, and for
every such basis the retained fibres `b65z_fiber D B` are the fibres of an element of
`g32h_PrymFamily` indexed by the polydisc, with the tuple matrices of `g`.
Source: G32 v0.16, Lemma 3.6 (lem:sixfold), Proposition 3.1 (Chevalley–Weil) and Lemma 3.3;
`b63gR_family` and `b63d_lattice_rank` at `mr_base`. -/
theorem b65z_prym_family (c : Fin 10 → ℂ) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g) :
    Nonempty (Module.Basis (Fin 12) ℤ (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c))) ∧
    ∀ B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)), ∃ P : g32h_PrymFamily, b65z_IsLocalPrym D B P :=
  b65z_prym_family_aux c g hg D

example := @b65z_prym_family

/-- **Theorem A along the G32 path, transport route (lower-level implication).** The marking
`m, hJ, hpair` and the fibre polarization `hpol` stay binders; the premise-removing wrapper that
feeds `b65z_marking` and `b65z_polarization` is planned, not frozen. The restatement of
`b63gU_theoremA_of_transport` with the retained family about `b65z_centre p` in place of `mr_base`: the
Prym family `P` of its fibres, the curve `b65p_curve p` of the 5c record `O`, and the
codifferential at the local period function `b65z_period`; `curve_zero` holds at the new centre.
Source: `g32a_theoremA`, `hk7_spread`; G32 v0.16, Theorem A and Lemma 2.2; `b65z_local_period`; `g32r_PeriodMap`. -/
theorem b65z_theoremA_of_transport (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily (b65z_centre p) g)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (h46 : g32s_Prop46 P)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) = b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b65z_period D (b65z_s₀ (b65z_centre p)) m) (b65p_curve p θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b65z_theoremA_of_transport_aux p O D B P hP F hF h46 m hJ hpair jet jet_certified codiff hpol transport A W pol

example := @b65z_theoremA_of_transport

/-- **Theorem A along the G32 path, reverse route (lower-level implication).** The marking
`m, hJ, hpair` and the fibre polarization `hpol` stay binders; the premise-removing wrapper that
feeds `b65z_marking` and `b65z_polarization` is planned, not frozen. The restatement of
`b63gU_theoremA_of_reverse` with the retained family about `b65z_centre p` in place of `mr_base`: the
Prym family `P` of its fibres, the curve `b65p_curve p` of the 5c record `O`, and the
codifferential at the local period function `b65z_period`; `curve_zero` holds at the new centre.
Source: `g32n_theoremA_of_premises`, `hk7_spread_of_members`; G32 v0.16, Theorem A and Lemma 2.2; `b65z_local_period`; `g32r_PeriodMap`. -/
theorem b65z_theoremA_of_reverse (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily (b65z_centre p) g)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (h46 : g32s_Prop46 P)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) = b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b65z_period D (b65z_s₀ (b65z_centre p)) m) (b65p_curve p θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (reverse : ∀ P Q, g32t_IsMember P → g32t_IsMember Q → g32t_KIsog P Q → g32t_KIsog Q P)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b65z_theoremA_of_reverse_aux p O D B P hP F hF h46 m hJ hpair jet jet_certified codiff hpol reverse A W pol

example := @b65z_theoremA_of_reverse

/-- **Theorem A along the G32 path, qinv route (lower-level implication).** The marking
`m, hJ, hpair` and the fibre polarization `hpol` stay binders; the premise-removing wrapper that
feeds `b65z_marking` and `b65z_polarization` is planned, not frozen. The restatement of
`b63gU_theoremA_of_qinv` with the retained family about `b65z_centre p` in place of `mr_base`: the
Prym family `P` of its fibres, the curve `b65p_curve p` of the 5c record `O`, and the
codifferential at the local period function `b65z_period`; `curve_zero` holds at the new centre.
Source: `qinv_g32_theoremA_of_premises`, `hk7_spread_of_witness`; G32 v0.16, Theorem A; Mumford, *Abelian Varieties*, §4; `b65z_local_period`; `g32r_PeriodMap`. -/
theorem b65z_theoremA_of_qinv (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily (b65z_centre p) g)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (h46 : g32s_Prop46 P)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) = b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b65z_period D (b65z_s₀ (b65z_centre p)) m) (b65p_curve p θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (qinv : qinv_premise)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b65z_theoremA_of_qinv_aux p O D B P hP F hF h46 m hJ hpair jet jet_certified codiff hpol qinv A W pol

example := @b65z_theoremA_of_qinv

/-- **Consistency of the routes.** A Prym family indexed by the retained fibres forces the tuple
of the family into the G32 Nielsen class, so the routes need no separate tuple hypothesis. -/
example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P) :
    g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) := by
  obtain ⟨j, hj⟩ := hP
  rw [← (hj (b65z_s₀ c)).1]
  exact P.tuple_nielsen _

/-- **Non-degeneracy.** Every fibre of a Prym family indexed by the retained fibres has dimension
six and Hodge numbers three and three, so the lattice is not of rank zero, and the index type is
the nonempty polydisc. -/
example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P) :
    Nonempty P.S ∧ ∀ s, (dim (P.fiber s).X.left : ℤ) = 6 ∧
      ((g32h_h10 (P.fiber s) : ℝ) = 3 ∧ (g32h_h01 (P.fiber s) : ℝ) = 3 ∨
        (g32h_h01 (P.fiber s) : ℝ) = 3 ∧ (g32h_h10 (P.fiber s) : ℝ) = 3) := by
  obtain ⟨j, -⟩ := hP
  refine ⟨⟨j (b65z_s₀ c)⟩, fun s ↦ ⟨?_, ?_⟩⟩
  · rw [P.dim_eq s, g32h_multCW_of_nielsen _ (P.tuple_nielsen s)]
  · have h := P.hodge s
    rw [g32h_multCW_of_nielsen _ (P.tuple_nielsen s),
      g32h_holoCW_of_nielsen _ (P.tuple_nielsen s)] at h
    norm_num at h
    exact h

/-- **Consumer compatibility check for `g32r_PeriodMap`.** The output types of
`b65z_local_period` at the G32 centre fit the fields of `g32r_PeriodMap`: the open polydisc about
`b65z_centre p`, the local period function, the fibre isogenies through `hP`, the curve
`b65p_curve p` of the 5c record and `curve_zero` at the new centre; `jet`, `jet_certified` and
`codiff` are binders stated for this same curve and period function. It checks the interface,
not a supply of the inputs: the marking stays a binder. This is the domain that
`b6t_polydisc mr_base` could not supply. -/
example (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily (b65z_centre p) g)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) = b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b65z_period D (b65z_s₀ (b65z_centre p)) m) (b65p_curve p θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T) :
    Nonempty (g32r_PeriodMap F P) := by
  obtain ⟨j, hj⟩ := hP
  have hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) := by
    rw [← (hj (b65z_s₀ _)).1]
    exact P.tuple_nielsen _
  obtain ⟨han, hch, hiso⟩ := b65z_local_period _ g hg D m hJ hpair
  exact ⟨{ V := b6t_polydisc (b65z_centre p),
            isOpen_V := b65z_polydisc_open _,
            period := b65z_period D (b65z_s₀ (b65z_centre p)) m,
            analytic := han,
            mapsTo := fun t ht ↦ (hch t ht).1,
            isog := fun t ht ↦ ⟨j ⟨t, ht⟩, by
              rw [(hj ⟨t, ht⟩).2, hF]
              exact hiso B ⟨t, ht⟩ _⟩,
            curve := b65p_curve p,
            curve_cont := O.curve_cont,
            curve_zero := b65z_centre_mem _,
            jet := jet,
            jet_certified := jet_certified,
            codiff := codiff }⟩

end HodgeLean.Foundations.Program
