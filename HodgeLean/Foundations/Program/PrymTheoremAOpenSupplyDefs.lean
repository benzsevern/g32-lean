import HodgeLean.Foundations.Program.PrymTheoremAIsog

/-! # Theorem A from an open retained supply
Implication from algebraic fibres above a nonempty open locus to Theorem A.
The geometric supply remains open. HC no distance; AV milestone no distance.
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

/-- An open retained supply, with an actual fibre selected above every point.
Source: G32 v0.16, proof of Theorem 7.2; `g32r_dominant`.
-/
structure b63gV_OpenSupply (D : rf8_SharedFamily) (F : g32m_UniversalFamily) where
  U : Set g32m_Domain
  isOpen : IsOpen U
  nonempty : U.Nonempty
  fibre : U → (b63gR_family D).S
  isog : ∀ m : U, g32t_KIsog ((b63gR_family D).fiber (fibre m)) (F.univ m.val)
  algebraic : ∀ m : U, g32t_WeilAlg ((b63gR_family D).fiber (fibre m))

example (D : rf8_SharedFamily) (F : g32m_UniversalFamily)
    (B : b63gV_OpenSupply D F) : B.U.Nonempty := B.nonempty

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

/-- Chain check toward the open-locus input of the transfer. -/
example (D : rf8_SharedFamily) (F : g32m_UniversalFamily)
    (B : b63gV_OpenSupply D F)
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q)) :
    ∀ m ∈ B.U, g32t_WeilAlg (F.univ m) := by
  intro m hm
  exact (transport _ _ (B.isog ⟨m, hm⟩)).1 (B.algebraic ⟨m, hm⟩)


/-- Chain check with the exact type of the `spread` field of `g32a_premises`. -/
example (D : rf8_SharedFamily) (F : g32m_UniversalFamily)
    (hF : F.univ = b60b_univ) (B : b63gV_OpenSupply D F)
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q)) :
    ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧
      {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C := by
  have hAlg : ∀ m ∈ B.U, g32t_WeilAlg (F.univ m) := by
    intro m hm
    exact (transport _ _ (B.isog ⟨m, hm⟩)).1 (B.algebraic ⟨m, hm⟩)
  refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
  · rintro Z rfl
    exact isClosedAnalytic_univ
  · rw [Set.sUnion_singleton, Set.eq_univ_iff_forall, hF]
    rw [hF] at hAlg
    exact hk_weilAlg_of_open B.isOpen B.nonempty hAlg

end HodgeLean.Foundations.Program
