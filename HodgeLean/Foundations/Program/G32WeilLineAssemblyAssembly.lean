import HodgeLean.Foundations.Program.G32WeilLineAssemblySchoen
import HodgeLean.Foundations.Program.G32ContractionTwoProofs
import HodgeLean.Foundations.Program.G32ContractionRestored
import HodgeLean.Foundations.Program.G32ContractionSupplier
import HodgeLean.Foundations.Program.G32WeilLineAssemblyExpansion
import HodgeLean.Foundations.Program.CycleFoundationsIntegration
import HodgeLean.Foundations.Program.G32RepTransport
import HodgeLean.Foundations.Program.CycleFoundations
import HodgeLean.Foundations.Program.CyclotomicWeilLinear

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf algebraicCycleClassSpan

theorem g32c_weilLine_assembly (A : g32t_Sixfold) (X : g32p_Cover A)
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
  classical
  letI := (torusCohomology_cupProductOf A.X).finite
  obtain ⟨S₀, χ₀, τ, τbar, θ, hτ, hθ, hdτ, hdθ, hρ, hall, hrows⟩ := hComparison
  have hE : g32c_Enumeration τ τbar θ := ⟨hτ, hθ, hdτ, hdθ, hall⟩
  let a := fun i => papersA τ τbar θ (S₀ i).H (χ₀ i)
  have ha := g32c_printed_sum a (fun i => (hrows i).2.2)
  obtain ⟨r, f, ε, hf⟩ := g32c_signed_expansion (fun i => (g32c_vectorRow i).n) a
  have hid : ∑ j, (ε j : ℤ) • a (f j) = (Pi.single (2 : Fin 44) 1, 0) := hf.trans ha
  let S := fun j => S₀ (f j)
  let χc := fun j => χ₀ (f j)
  have hχc := fun j => (hrows (f j)).1
  have hAdm : ∀ j, g32p_Admissible X.aut (S j) := by
    intro j
    apply hAdmissible
    obtain ⟨v, hv, hi, hm, ho, he⟩ := (hrows (f j)).2.1
    exact ⟨v, hv, hm, ho, he⟩
  obtain ⟨δ, hδ⟩ := g32c_gamma_invariant X S hAdm χc hχc τ τbar θ hE 2 hρ ε hid
  choose t ht using fun j => hEmbedding (S j) (δ * ε j)
  have hZex (j : Fin r) := Submodule.exists_mem_ne_zero_of_ne_bot (hComplement (S j) (hAdm j) (t j))
  choose Z hZ hZ0 using hZex
  letI (j : Fin r) := (torusCohomology_cupProductOf (g32c_parts X S hAdm j)).finite
  choose y hy hy0 hyalg using fun j => g32c_schoen_wedge_exists A X hS (S j) (hAdm j)
  let p := ∑ j, (X.part (S j) (hAdm j)).k
  let d := ∑ j, (X.part (S j) (hAdm j)).k * (S j).m.totient
  let c := 3 + ∑ j, (X.part (S j) (hAdm j)).k * ((S j).m.totient - 1)
  have hp : 2 * p = ∑ j, 2 * (X.part (S j) (hAdm j)).k := Finset.mul_sum _ _ _
  have hc : 2 * c = 2 * 3 + ∑ j, 2 * (X.part (S j) (hAdm j)).k * ((S j).m.totient - 1) := by
    simp only [c, Nat.mul_add, Finset.mul_sum, Nat.mul_assoc]
  have hsum : (∑ j, (X.part (S j) (hAdm j)).k * ((S j).m.totient - 1)) + p = d := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hm := Nat.totient_pos.mpr (NeZero.pos (S j).m)
    calc
      _ = (X.part (S j) (hAdm j)).k * (((S j).m.totient - 1) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel hm]
  have hdeg : 2 * c + 2 * p = 2 * 3 + 2 * d := by dsimp [c]; omega
  have hB := hDegree S hAdm
  obtain ⟨I, hI⟩ := cfd_top_integration (g32c_B X S hAdm) d hB
  have hY := hProduct S hAdm y hyalg p hp
  obtain ⟨α, hα, hcontract⟩ := g32c_contraction_line_aux X S hAdm d hB I c p 3 hdeg hc hp
    t Z hZ hZ0 y hy hy0
  intro v hv
  obtain ⟨w, hw, rfl⟩ := hv
  have hGamma := g32c_gamma_algebraic_aux X hM S hAdm c
    (g32c_gammaAbs (w : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ A.X 1)) fun j => (Z j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hAdm j) 1)))
    (hδ t ht w hw Z hZ)
  have hmem := g32c_corrC_span_aux A.X (g32c_B X S hAdm) d hB I c p 3 hdeg _ hGamma _ hY
  rw [hcontract w] at hmem
  let P : Submodule ℂ (ℂ ⊗[ℚ] HQ A.X 6) :=
    (algebraicCycleClassSpan A.X 3).baseChange ℂ
  have hm := (Submodule.smul_mem_iff (S := ℂ) P hα).mp hmem
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using hm

end HodgeLean.Foundations.Program
