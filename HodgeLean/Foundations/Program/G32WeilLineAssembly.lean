import HodgeLean.Foundations.Program.G32WeilLineAssemblyProofs

/-! # Assembly of the degree-six Weil line (FROZEN SPEC)

Implication from the explicit literature and assembly inputs. The character comparison,
admissibility, embeddings, complementary generators, product algebraicity and degree count
are explicit binders on the assembly. Restored character statements are planned dependencies.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

/-- A prescribed primitive root determines a cyclotomic embedding.
Source: G32 v0.16, proof of Proposition 4.6, paragraph The correspondence;
cyclotomic extension universal property. -/
theorem g32c_embedding_exists (S : g32p_Supplier) (k : ℤˣ) :
    ∃ t : cyc_Field S.m →ₐ[ℚ] ℂ,
      t (g32p_zeta S) = g32p_root S.m ^ (k : ℤ) :=
  g32c_embedding_exists_aux S k

example (S : g32p_Supplier) (k : ℤˣ) :
    ∃ t : cyc_Field S.m →ₐ[ℚ] ℂ,
      t (g32p_zeta S) = g32p_root S.m ^ (k : ℤ) :=
  g32c_embedding_exists S k

/-- The top exterior power of the sum of all other embedding spaces is nonzero.
Source: G32 v0.16, proof of Proposition 4.6, paragraph The correspondence;
Bourbaki, Algebra, Ch. III, §7.7; `cyc_eigenline_decomposition`. -/
theorem g32c_coLine_ne_bot {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {m h : ℕ} [NeZero m]
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    g32c_coLine e t (h * (m.totient - 1)) ≠ ⊥ :=
  g32c_coLine_ne_bot_aux e t

example {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {m h : ℕ} [NeZero m]
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    g32c_coLine e t (h * (m.totient - 1)) ≠ ⊥ :=
  g32c_coLine_ne_bot e t

/-- A supplier with one of the printed witness rows is admissible on a realized cover.
Source: G32 v0.16, Subsection 4.2, Proposition 4.5 and Appendix B;
Proposition 3.1 and Definition 4.1. -/
theorem g32c_supplier_admissible (A : g32t_Sixfold) (X : g32p_Cover A)
    (S : g32p_Supplier)
    (hrow : ∃ r ∈ g32WitnessTable, r.m = S.m ∧ r.orderH = Nat.card S.H ∧
      (g32p_exponents S).Perm (expandExps r.exps)) :
    g32p_Admissible X.aut S :=
  g32c_supplier_admissible_aux A X S hrow

example (A : g32t_Sixfold) (X : g32p_Cover A)
    (S : g32p_Supplier)
    (hrow : ∃ r ∈ g32WitnessTable, r.m = S.m ∧ r.orderH = Nat.card S.H ∧
      (g32p_exponents S).Perm (expandExps r.exps)) :
    g32p_Admissible X.aut S :=
  g32c_supplier_admissible A X S hrow

/-- The dimension of the supplier product is the sum of the cyclotomic factor dimensions.
Source: G32 v0.16, proof of Proposition 4.6, paragraph Degrees;
Birkenhake–Lange, Complex Abelian Varieties, §1.3; `cfd_product_dimension`. -/
theorem g32c_degree_count (A : g32t_Sixfold) (X : g32p_Cover A) {r : ℕ}
    (S : Fin r → g32p_Supplier) (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    TopologicalSpace.dim (g32c_B X S hS).left =
      (∑ j, (X.part (S j) (hS j)).k * (S j).m.totient : ℕ) :=
  g32c_degree_count_aux A X S hS

example (A : g32t_Sixfold) (X : g32p_Cover A) {r : ℕ}
    (S : Fin r → g32p_Supplier) (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    TopologicalSpace.dim (g32c_B X S hS).left =
      (∑ j, (X.part (S j) (hS j)).k * (S j).m.totient : ℕ) :=
  g32c_degree_count A X S hS

/-- Products of algebraic supplier classes lie in the complex algebraic span of the product.
Source: Fulton, Intersection Theory, §8.1 and §19.1;
`cfd_hom_pullback_span`, `hc9k_cycleClassMultiplicative`; G32 v0.16, Proposition 4.6. -/
theorem g32c_schoen_product_span (A : g32t_Sixfold) (X : g32p_Cover A) {r : ℕ}
    (S : Fin r → g32p_Supplier) (hS : ∀ j, g32p_Admissible X.aut (S j))
    (y : ∀ j, ⋀[ℚ]^(2 * (X.part (S j) (hS j)).k) (HQ (g32c_parts X S hS j) 1))
    (hy : ∀ j, (cupProductOf (g32c_parts X S hS j)).cupWedgeMap _ (y j) ∈
      algebraicCycleClassSpan (g32c_parts X S hS j) (X.part (S j) (hS j)).k)
    (p : ℕ) (hp : 2 * p = ∑ j, 2 * (X.part (S j) (hS j)).k) :
    g32c_classB X S hS (2 * p) (g32c_prodAbs fun j =>
      (HodgeBlocks.complexifyWedge _ (y j) :
        ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))) ∈
      (algebraicCycleClassSpan (g32c_B X S hS) p).baseChange ℂ :=
  g32c_schoen_product_span_aux A X S hS y hy p hp

example (A : g32t_Sixfold) (X : g32p_Cover A) {r : ℕ}
    (S : Fin r → g32p_Supplier) (hS : ∀ j, g32p_Admissible X.aut (S j))
    (y : ∀ j, ⋀[ℚ]^(2 * (X.part (S j) (hS j)).k) (HQ (g32c_parts X S hS j) 1))
    (hy : ∀ j, (cupProductOf (g32c_parts X S hS j)).cupWedgeMap _ (y j) ∈
      algebraicCycleClassSpan (g32c_parts X S hS j) (X.part (S j) (hS j)).k)
    (p : ℕ) (hp : 2 * p = ∑ j, 2 * (X.part (S j) (hS j)).k) :
    g32c_classB X S hS (2 * p) (g32c_prodAbs fun j =>
      (HodgeBlocks.complexifyWedge _ (y j) :
        ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))) ∈
      (algebraicCycleClassSpan (g32c_B X S hS) p).baseChange ℂ :=
  g32c_schoen_product_span A X S hS y hy p hp

/-- The degree-six Weil line lies in the complex algebraic span, from the named literature
inputs and the six explicit assembly obligations. The conclusion is exactly the frozen
`g32p_weilLine_algebraic` conclusion on `spec/p46`.
Source: G32 v0.16, Proposition 4.6, proof lines 296–322; Schoen (1988), Theorem 2.0
and Corollary 3.1; Milne (1999), Theorem 3.2 and Lemma 3.1. -/
theorem g32c_weilLine_algebraic (A : g32t_Sixfold) (X : g32p_Cover A)
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
    g32p_wedgeClasses A.X A.W.Vs 6 ≤ (algebraicCycleClassSpan A.X 3).baseChange ℂ :=
  g32c_weilLine_algebraic_aux A X hS hM hComparison hAdmissible hEmbedding hComplement hProduct hDegree

/-- A degree-six wedge on the specified subspace has its cup image in the target carrier. -/
example (A : g32t_Sixfold) (w : ⋀[ℂ]^6 (ℂ ⊗[ℚ] HQ A.X 1))
    (hw : w ∈ LinearMap.range (exteriorPower.map 6 A.W.Vs.subtype)) :
    letI := (torusCohomology_cupProductOf A.X).finite
    ((cupProductOf A.X).cupWedgeMap 6).baseChange ℂ
        ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv 6).symm w) ∈
      g32p_wedgeClasses A.X A.W.Vs 6 := by
  exact ⟨w, hw, rfl⟩

end HodgeLean.Foundations.Program
