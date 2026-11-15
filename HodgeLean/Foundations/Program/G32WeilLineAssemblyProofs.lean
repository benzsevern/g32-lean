import HodgeLean.Foundations.Program.G32WeilLineAssemblyAssembly
import HodgeLean.Foundations.Program.G32WeilLineAssemblyProductProof
import HodgeLean.Foundations.Program.G32WeilLineAssemblyPositive

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

theorem g32c_embedding_exists_aux (S : g32p_Supplier) (k : ℤˣ) :
    ∃ t : cyc_Field S.m →ₐ[ℚ] ℂ,
      t (g32p_zeta S) = g32p_root S.m ^ (k : ℤ) := by
  have hz : IsPrimitiveRoot (g32p_zeta S) S.m :=
    IsCyclotomicExtension.zeta_spec S.m ℚ (cyc_Field S.m)
  have hr : IsPrimitiveRoot (g32p_root S.m ^ (k : ℤ)) S.m := by
    have hr := Complex.isPrimitiveRoot_exp S.m (NeZero.ne S.m)
    change IsPrimitiveRoot (g32p_root S.m) S.m at hr
    rcases Int.isUnit_eq_one_or k.isUnit with hk | hk
    · simpa only [hk, zpow_one] using hr
    · simpa only [hk, zpow_neg_one] using hr.inv
  let E := hz.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos S.m))
  let z : primitiveRoots S.m ℂ := ⟨_, (mem_primitiveRoots (NeZero.pos S.m)).mpr hr⟩
  refine ⟨E.symm z, ?_⟩
  exact congrArg Subtype.val (E.apply_symm_apply z)

theorem g32c_coLine_ne_bot_aux {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {m h : ℕ} [NeZero m]
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    g32c_coLine e t (h * (m.totient - 1)) ≠ ⊥ := by
  have hr := HodgeBlocks.finrank_range_exteriorPower_map_subtype_of_finrank
    ℂ (ℂ ⊗[ℚ] V) (⨆ (s) (_ : s ≠ t), cyc_eigenspace e s)
    (h * (m.totient - 1)) (g32rep_finrank_coSum e t)
  intro hz
  change Module.finrank ℂ ↥(g32c_coLine e t (h * (m.totient - 1))) = 1 at hr
  rw [hz, finrank_bot] at hr
  omega

theorem g32c_supplier_admissible_aux (A : g32t_Sixfold) (X : g32p_Cover A)
    (S : g32p_Supplier)
    (hrow : ∃ r ∈ g32WitnessTable, r.m = S.m ∧ r.orderH = Nat.card S.H ∧
      (g32p_exponents S).Perm (expandExps r.exps)) :
    g32p_Admissible X.aut S := by
  refine ⟨g32c_supplier_simple S hrow, ?_⟩
  apply g32c_primitive_ne_bot_of_eigen A X S
  obtain ⟨I, _, σ, hσ, hdist, hcov⟩ := rfd_simple_family g32p_G
  rw [g32c_supplier_rank_positive_iff A X S σ hσ hdist hcov]
  exact g32c_supplier_cw_positive S σ hσ hdist hcov

theorem g32c_degree_count_aux (A : g32t_Sixfold) (X : g32p_Cover A) {r : ℕ}
    (S : Fin r → g32p_Supplier) (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    TopologicalSpace.dim (g32c_B X S hS).left =
      (∑ j, (X.part (S j) (hS j)).k * (S j).m.totient : ℕ) := by
  letI := (torusCohomology_cupProductOf (g32c_B X S hS)).finite
  letI (j : Fin r) := (torusCohomology_cupProductOf (g32c_parts X S hS j)).finite
  obtain ⟨hπ⟩ := cfd_product_limit r (g32c_parts X S hS)
  have hb := cfd_kunneth_one r (g32c_parts X S hS) (g32c_B X S hS)
    (cfd_proj r (g32c_parts X S hS)) hπ
  have he := (LinearEquiv.ofBijective _ hb).finrank_eq
  rw [Module.finrank_pi_fintype,
    (torusCohomology_cupProductOf (g32c_B X S hS)).finrank_eq] at he
  have hf (j : Fin r) : Module.finrank ℚ (HQ (g32c_parts X S hS j) 1) =
      2 * ((X.part (S j) (hS j)).k * (S j).m.totient) := by
    rw [(X.part (S j) (hS j)).act.cyc_coordinates.finrank_eq,
      Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      cyc_finrank_field]
    exact Nat.mul_assoc _ _ _
  simp_rw [hf] at he
  rw [← Finset.mul_sum] at he
  exact_mod_cast Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) he.symm


theorem g32c_schoen_product_span_aux (A : g32t_Sixfold) (X : g32p_Cover A) {r : ℕ}
    (S : Fin r → g32p_Supplier) (hS : ∀ j, g32p_Admissible X.aut (S j))
    (y : ∀ j, ⋀[ℚ]^(2 * (X.part (S j) (hS j)).k) (HQ (g32c_parts X S hS j) 1))
    (hy : ∀ j, (cupProductOf (g32c_parts X S hS j)).cupWedgeMap _ (y j) ∈
      algebraicCycleClassSpan (g32c_parts X S hS j) (X.part (S j) (hS j)).k)
    (p : ℕ) (hp : 2 * p = ∑ j, 2 * (X.part (S j) (hS j)).k) :
    g32c_classB X S hS (2 * p) (g32c_prodAbs fun j =>
      (HodgeBlocks.complexifyWedge _ (y j) :
        ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))) ∈
      (algebraicCycleClassSpan (g32c_B X S hS) p).baseChange ℂ := by
  exact g32c_schoen_product_span_main A X S hS y hy p hp

theorem g32c_weilLine_algebraic_aux (A : g32t_Sixfold) (X : g32p_Cover A)
    (hS : g32p_SchoenSupplier X)
    (hM : g32p_MilneInvariance X.J X.pol X.pol_nondeg X.pol_pos)
    (hComparison : ∃ (S : Fin 51 → g32p_Supplier) (χc : ∀ i, (S i).H →* ℂˣ)
      (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G),
      (∀ j, Simple (τ j) ∧ Simple (τbar j) ∧ ¬ g32p_SelfDual (τ j) ∧
        (∀ g, (τbar j).character g = star ((τ j).character g)) ∧ 0 < g32p_cwMult (τ j)) ∧
      (∀ j, Simple (θ j) ∧ g32p_Quaternionic (θ j) ∧ 0 < g32p_cwMult (θ j)) ∧
      (∀ j k, j ≠ k → IsEmpty (τ j ≅ τ k) ∧ IsEmpty (τ j ≅ τbar k)) ∧
      (∀ j k : Fin 4, j ≠ k → IsEmpty (θ j ≅ θ k)) ∧
      Nonempty (τ 2 ≅ g32p_rho) ∧
      (∀ σ : FDRep ℂ g32p_G, Simple σ → 0 < g32p_cwMult σ →
        (¬ g32p_SelfDual σ → ∃ j, Nonempty (σ ≅ τ j) ∨ Nonempty (σ ≅ τbar j)) ∧
        (g32p_Quaternionic σ → ∃ j, Nonempty (σ ≅ θ j))) ∧
      ∀ i : Fin 51,
        (∀ h, ((χc i h : ℂˣ) : ℂ) =
          g32p_root (S i).m ^ (Multiplicative.toAdd ((S i).χ h)).val) ∧
        (∃ r ∈ g32WitnessTable, r.i = i.val + 1 ∧ r.m = (S i).m ∧
          r.orderH = Nat.card (S i).H ∧ (g32p_exponents (S i)).Perm (expandExps r.exps)) ∧
        ∃ v ∈ g32VectorTable, v.i = i.val + 1 ∧
          papersA τ τbar θ (S i).H (χc i) = g32SparseVec v.coords)
    (hAdmissible : ∀ (S : g32p_Supplier),
      (∃ r ∈ g32WitnessTable, r.m = S.m ∧ r.orderH = Nat.card S.H ∧
        (g32p_exponents S).Perm (expandExps r.exps)) → g32p_Admissible X.aut S)
    (hEmbedding : ∀ (S : g32p_Supplier) (k : ℤˣ),
      ∃ t : cyc_Field S.m →ₐ[ℚ] ℂ, t (g32p_zeta S) = g32p_root S.m ^ (k : ℤ))
    (hComplement : ∀ (S : g32p_Supplier) (hS' : g32p_Admissible X.aut S)
      (t : cyc_Field S.m →ₐ[ℚ] ℂ),
      g32c_coLine (X.part S hS').act.cyc_coordinates t
        (2 * (X.part S hS').k * (S.m.totient - 1)) ≠ ⊥)
    (hProduct : ∀ {r : ℕ}
    (S : Fin r → g32p_Supplier) (hS : ∀ j, g32p_Admissible X.aut (S j))
    (y : ∀ j, ⋀[ℚ]^(2 * (X.part (S j) (hS j)).k) (HQ (g32c_parts X S hS j) 1))
    (_hy : ∀ j, (cupProductOf (g32c_parts X S hS j)).cupWedgeMap _ (y j) ∈
      algebraicCycleClassSpan (g32c_parts X S hS j) (X.part (S j) (hS j)).k)
    (p : ℕ) (_hp : 2 * p = ∑ j, 2 * (X.part (S j) (hS j)).k),
    g32c_classB X S hS (2 * p) (g32c_prodAbs fun j =>
      (HodgeBlocks.complexifyWedge _ (y j) :
        ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))) ∈
      (algebraicCycleClassSpan (g32c_B X S hS) p).baseChange ℂ)
    (hDegree : ∀ {r : ℕ} (S : Fin r → g32p_Supplier)
      (hS' : ∀ j, g32p_Admissible X.aut (S j)),
      TopologicalSpace.dim (g32c_B X S hS').left =
        (∑ j, (X.part (S j) (hS' j)).k * (S j).m.totient : ℕ)) :
    letI := (torusCohomology_cupProductOf A.X).finite
    g32p_wedgeClasses A.X A.W.Vs 6 ≤ (algebraicCycleClassSpan A.X 3).baseChange ℂ := by
  exact g32c_weilLine_assembly A X hS hM hComparison hAdmissible hEmbedding hComplement
    hProduct hDegree

end HodgeLean.Foundations.Program
