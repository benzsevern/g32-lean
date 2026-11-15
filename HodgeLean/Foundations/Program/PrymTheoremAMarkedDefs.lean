import HodgeLean.Foundations.Program.PrymParabolicGeometricMarking
import HodgeLean.Foundations.Program.PrymTheoremAComposed
import HodgeLean.Foundations.Program.PeriodFibreMarking

/-! # Coordinates for the Prym isogeny interface
Implication from retained geometric data to the named coordinate function.
HC no distance; AV milestone no distance.
-/
noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- The rational marking selected from retained based root monodromy.
Source: `hg7g_rational_marking`. -/
def b63gW_marking (D : rf8_SharedFamily)
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) :
    (ℚ ⊗[ℤ] b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice) :=
  Classical.choose (hg7g_rational_marking D u₀ hroot)

example (D : rf8_SharedFamily)
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) :
    b63gW_marking D u₀ hroot = Classical.choose (hg7g_rational_marking D u₀ hroot) := rfl

/-- The shared-family coordinate at the fixed reference parameter.
Source: `b64i_period`, `b63gP_s₀`. -/
def b63gW_period (D : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
 : (Fin 10 → ℂ) → (Fin 9 → ℂ) :=
  b64i_period D b63gP_s₀ m

example (D : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
 : b63gW_period D m = b64i_period D b63gP_s₀ m := rfl

/-- Checked shared-cover inputs for the based marking, with positive lattice rank.
This example uses only existing statements with bodies. -/
example : ∃ (R : rf8_SharedFamily) (u₀ : R.atlas.π ⁻¹' {b63gP_basePoint}),
    (∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) ∧
    Module.finrank ℤ (b63l_parameterLattice mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀) = 12 ∧ b4b_root 0 ≠ 1 := by
  obtain ⟨R, y₀, γ, u₀, hγ, hroot⟩ := rf8_shared_root
  have hy : y₀ = b63gP_basePoint := by
    apply Subtype.ext
    obtain ⟨p, hp, -⟩ := hγ 12
    calc
      (y₀ : OnePoint ℂ) = mr_curve 12 0 := by simpa using hp 0
      _ = (b63gP_basePoint : OnePoint ℂ) := by
        change mr_curve 12 0 = ((mr_basePoint : ℂ) : OnePoint ℂ)
        simp [mr_curve, mr_outer, mr_basePoint]
  subst y₀
  have hγeq : γ = b63gP_loops := by
    funext i
    exact (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).unique
      (hγ i) (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec
  subst γ
  refine ⟨R, u₀, hroot, ?_, ?_⟩
  · rw [Module.finrank_eq_card_basis (b63gR_basis R), Fintype.card_fin]
  · intro h
    have ho := b63_root_order (0 : Fin 13)
    rw [h, orderOf_one] at ho
    norm_num at ho

/-- Every retained fibre has dimension six and Hodge numbers three and three. -/
example (R : rf8_SharedFamily) (t : (b63gR_family R).S) :
    dim ((b63gR_family R).fiber t).X.left = 6 ∧
      g32h_h10 ((b63gR_family R).fiber t) = 3 ∧
      g32h_h01 ((b63gR_family R).fiber t) = 3 :=
  ⟨(g32h_fiber_polarized _ t).dim_eq, g32h_h10_eq_three _ t⟩

/-- A nonidentity tuple entry excludes the trivial monodromy case. -/
example (R : rf8_SharedFamily) (t : (b63gR_family R).S) (i : Fin 13) :
    (b63gR_family R).tuple t i ≠ 1 := by
  intro hi
  change b63g5_tuple i = 1 at hi
  have h1 : b4b_root i = 1 :=
    Subtype.val_injective (hi.trans (map_one b4b_toMatrix).symm)
  have h3 := b63_root_order i
  rw [h1, orderOf_one] at h3
  split_ifs at h3 <;> omega

/-- The universal-family equality used by S7 has a checked instance. -/
example : ∃ F : g32m_UniversalFamily, F.univ = b60b_univ :=
  ⟨{ univ := b60b_univ, member := b60b_member, cover := b60c_cover }, rfl⟩

/-- The existing rational marking with `b64e_hisog` fills the marking and isogeny binders of `b63gR_periodMap`; only
the curve, the certified jet and the codifferential comparison remain.
Source: `hg7g_rational_marking`, `b64e_hisog`, `b63gR_periodMap`. -/
example (R : rf8_SharedFamily)
    (u₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) (Fm : g32m_UniversalFamily) (hFm : Fm.univ = b60b_univ) :
    ∃ m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
        (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice),
      ∀ (curve : ℂ → Fin 10 → ℂ) (_ : ContinuousAt curve 0)
        (_ : curve 0 ∈ b6t_polydisc mr_base)
        (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (_ : g32r_CertifiedJet jet)
        (_ : ∀ᶠ θ in nhds (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
          ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
            jet θ = L * LinearMap.toMatrix'
              (fderiv ℂ (b64i_period R b63gP_s₀ m) (curve θ) :
                (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T),
        ∃ F : g32r_PeriodMap Fm (b63gR_family R),
          F.V = b6t_polydisc mr_base ∧ F.period = b64i_period R b63gP_s₀ m := by
  obtain ⟨m, hJ, hpair⟩ := hg7g_rational_marking R u₀ hroot
  exact ⟨m, fun curve hc h0 jet hjet hcod => b63gR_periodMap R m hJ hpair Fm
    (b64e_hisog R m hJ hpair Fm hFm) curve hc h0 jet hjet hcod⟩

end HodgeLean.Foundations.Program
