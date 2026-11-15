import HodgeLean.Foundations.Program.G32ContractionCrossC
import HodgeLean.Foundations.Program.G32ContractionClassMultiply
import HodgeLean.Foundations.Program.G32ContractionProductMultiply
import HodgeLean.Foundations.Program.G32ContractionProductClass
import HodgeLean.Foundations.Program.G32ContractionDescent
import HodgeLean.Foundations.Program.G32ContractionEquivariance
import HodgeLean.Foundations.Program.G32ContractionGrading
import HodgeLean.Foundations.Program.G32ContractionProjection
import HodgeLean.Foundations.Program.G32ContractionSpanTransport
import HodgeLean.Foundations.Program.G32ContractionScalar
import HodgeLean.Foundations.Program.G32ContractionTwoDefs
import HodgeLean.Foundations.Program.G32Contraction
import HodgeLean.Foundations.Program.G32RepTransport
import HodgeLean.Foundations.Program.CycleFoundationsSpans
import HodgeLean.Foundations.Program.CycleFoundationsPullback

/-! # Bodies of the second stage of the G32 contraction

One auxiliary body per statement of `G32ContractionTwo.lean`. HC no distance; AV milestone no
distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option Elab.async false

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

variable {A : g32t_Sixfold}

theorem g32c_proj_class_aux (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (n : ℕ)
    (x : ExteriorAlgebra ℂ ((ℂ ⊗[ℚ] HQ A.X 1) × ∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1)) :
    (homPullback (g32c_proj X S hS) n).baseChange ℂ (g32c_class X S hS n x) =
      g32p_powerClass X.J (r + 1) n (exteriorPower.map n (g32c_lowerOne X S hS)
        (DirectSum.decompose (fun i : ℕ => ⋀[ℂ]^i _) x n)) := by
  letI := (torusCohomology_cupProductOf (A.X ⊗ g32c_B X S hS)).finite
  letI := (torusCohomology_cupProductOf (g3_power X.J (r + 1))).finite
  simp only [g32c_class, g32p_powerClass, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [g32c_cupC_pullback]
  congr 2
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, g32c_proj_one,
    exteriorPower.map_comp, LinearMap.comp_apply]

theorem g32c_gamma_algebraic_aux (X : g32p_Cover A)
    (hM : g32p_MilneInvariance X.J X.pol X.pol_nondeg X.pol_pos) {r : ℕ}
    (S : Fin r → g32p_Supplier) (hS : ∀ j, g32p_Admissible X.aut (S j)) (c : ℕ)
    (x : ExteriorAlgebra ℂ ((ℂ ⊗[ℚ] HQ A.X 1) × ∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))
    (hx : ∀ u ∈ g32c_U X, g32c_factorAction (g32c_restrict X.inclA X.projA X.NA u)
        (fun j => g32c_restrict (X.part (S j) (hS j)).incl (X.part (S j) (hS j)).proj
          (X.part (S j) (hS j)).N u) x = x) :
    g32c_class X S hS (2 * c) x ∈
      (algebraicCycleClassSpan (A.X ⊗ g32c_B X S hS) c).baseChange ℂ := by
  let v := exteriorPower.map (2 * c) (g32c_lowerOne X S hS)
    (DirectSum.decompose (fun i : ℕ => ⋀[ℂ]^i _) x (2 * c))
  have hInv : g32p_powerClass X.J (r + 1) (2 * c) v ∈
      g32p_invariants X.J X.pol (r + 1) (2 * c) := by
    unfold g32p_invariants
    apply Submodule.mem_map.mpr
    refine ⟨v, ?_, rfl⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply]
    intro u hu
    have hU : u ∈ g32c_U X :=
      ⟨hu.1, fun g => hu.2.1 (X.aut g) (X.aut_hom g), hu.2.2⟩
    exact g32c_exterior_invariant_degree (g32c_lowerOne X S hS)
      (g32p_diag X.J u (r + 1)) _ (g32c_lowerOne_equivariant_aux X S hS hU)
      (2 * c) x (hx u hU)
  have hpull := hM.invariant (r + 1) c hInv
  change g32p_powerClass X.J (r + 1) (2 * c)
    (exteriorPower.map (2 * c) (g32c_lowerOne X S hS)
      (DirectSum.decompose (fun i : ℕ => ⋀[ℂ]^i _) x (2 * c))) ∈ _ at hpull
  rw [← g32c_proj_class_aux X S hS] at hpull
  letI : IsMonHom (g32c_incl X S hS) := (g32c_realization X S hS).1
  refine g32c_baseChange_retract_span
    (homPullback (g32c_proj X S hS) (2 * c)) (homPullback (g32c_incl X S hS) (2 * c))
    (algebraicCycleClassSpan (A.X ⊗ g32c_B X S hS) c)
    (algebraicCycleClassSpan (g3_power X.J (r + 1)) c) ((g32c_N X S hS : ℚ) ^ (2 * c))
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr (g32c_retraction X S hS).1.ne'))
    ((g32c_retraction X S hS).2.2 (2 * c)) ?_ _ hpull
  intro z hz
  have hz' : z ∈ cfd_cycleSpan (g3_power X.J (r + 1)) c := by rwa [g32c_cycleSpan_eq]
  have hh := cfd_hom_pullback_span (g3_power X.J (r + 1)) (A.X ⊗ g32c_B X S hS)
    (g32c_incl X S hS) c z hz'
  rwa [g32c_cycleSpan_eq] at hh


theorem g32c_contraction_line_aux (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (d : ℕ)
    (hB : TopologicalSpace.dim (g32c_B X S hS).left = d)
    (I : HQ (g32c_B X S hS) (2 * d) ≃ₗ[ℚ] ℚ) (c p q : ℕ) (h : 2 * c + 2 * p = 2 * q + 2 * d)
    (hc : 2 * c = 2 * q + ∑ j, 2 * (X.part (S j) (hS j)).k * ((S j).m.totient - 1))
    (hp : 2 * p = ∑ j, 2 * (X.part (S j) (hS j)).k)
    (t : ∀ j, cyc_Field (S j).m →ₐ[ℚ] ℂ)
    (Z : ∀ j, ⋀[ℂ]^(2 * (X.part (S j) (hS j)).k * ((S j).m.totient - 1))
      (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))
    (hZ : ∀ j, Z j ∈ g32c_coLine (X.part (S j) (hS j)).act.cyc_coordinates (t j)
      (2 * (X.part (S j) (hS j)).k * ((S j).m.totient - 1)))
    (hZ0 : ∀ j, Z j ≠ 0)
    (y : ∀ j, ⋀[ℚ]^(2 * (X.part (S j) (hS j)).k) (HQ (g32c_parts X S hS j) 1))
    (hy : ∀ j, y j ∈ cyc_wedges (X.part (S j) (hS j)).act.cyc_coordinates)
    (hy0 : ∀ j, y j ≠ 0) :
    letI := (torusCohomology_cupProductOf A.X).finite
    ∃ a : ℂ, a ≠ 0 ∧ ∀ w : ⋀[ℂ]^(2 * q) (ℂ ⊗[ℚ] HQ A.X 1),
      g32c_corrC A.X (g32c_B X S hS) d I c p q h
          (g32c_class X S hS (2 * c) (g32c_gammaAbs (w : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ A.X 1))
            fun j => (Z j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))))
          (g32c_classB X S hS (2 * p) (g32c_prodAbs fun j =>
            (HodgeBlocks.complexifyWedge _ (y j) :
              ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1)))) =
        a • ((cupProductOf A.X).cupWedgeMap (2 * q)).baseChange ℂ
          ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (2 * q)).symm w) := by
  letI := (torusCohomology_cupProductOf A.X).finite
  let nZ (j : Fin r) := 2 * (X.part (S j) (hS j)).k * ((S j).m.totient - 1)
  let ny (j : Fin r) := 2 * (X.part (S j) (hS j)).k
  let e := ∑ j, (X.part (S j) (hS j)).k * ((S j).m.totient - 1)
  have he : ∑ j, nZ j = 2 * e := by
    simp only [e, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [nZ]
    ring
  have hce : 2 * q + 2 * e = 2 * c := by
    change 2 * c = 2 * q + ∑ j, nZ j at hc
    rw [he] at hc
    exact hc.symm
  have hed : 2 * e + 2 * p = 2 * d := by omega
  let yc (j : Fin r) := HodgeBlocks.complexifyWedge (ny j) (y j)
  let z : ⋀[ℂ]^(2 * e) (∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1) :=
    ⟨g32c_prodAbs (fun j => (Z j : ExteriorAlgebra ℂ _)),
      he ▸ g32c_orderedProduct_mem _ nZ Z⟩
  let yy : ⋀[ℂ]^(2 * p) (∀ j, ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1) :=
    ⟨g32c_prodAbs (fun j => (yc j : ExteriorAlgebra ℂ _)),
      hp.symm ▸ g32c_orderedProduct_mem _ ny yc⟩
  let zz (j : Fin r) : ⋀[ℂ]^(nZ j + ny j) (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1) :=
    ⟨(Z j : ExteriorAlgebra ℂ _) * (yc j : ExteriorAlgebra ℂ _),
      SetLike.mul_mem_graded (Z j).property (yc j).property⟩
  have hzz (j : Fin r) : zz j ≠ 0 := by
    intro hz
    have hz' := congrArg Subtype.val hz
    exact g32c_coLine_mul_ne_zero (X.part (S j) (hS j)).act.cyc_coordinates
      (t j) (nZ j) (Z j) (hZ j) (hZ0 j) (y j) (hy j) (hy0 j) hz'
  have hn : ∑ j, (nZ j + ny j) = 2 * d := by
    rw [Finset.sum_add_distrib, he, ← hp]
    exact hed
  have hmul : (z : ExteriorAlgebra ℂ _) * (yy : ExteriorAlgebra ℂ _) =
      g32c_prodAbs (fun j => (zz j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))) := by
    let Z' (j : Fin r) : ⋀[ℂ]^(2 * ((X.part (S j) (hS j)).k *
        ((S j).m.totient - 1))) (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1) :=
      ⟨Z j, by convert (Z j).property using 1 <;> congr 1 <;> ring⟩
    exact g32c_prodAbs_mul_even _
      (fun j => (X.part (S j) (hS j)).k * ((S j).m.totient - 1))
      (fun j => (X.part (S j) (hS j)).k) Z' yc
  let a := TensorProduct.AlgebraTensorModule.rid ℚ ℂ ℂ
    (I.toLinearMap.baseChange ℂ (g32c_classB X S hS (2 * d)
      (g32c_prodAbs fun j => (zz j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1)))))
  refine ⟨a, ?_, ?_⟩
  · intro ha
    apply g32c_classB_prod_ne_zero_aux X S hS d I (fun j => nZ j + ny j) hn zz hzz
    exact (TensorProduct.AlgebraTensorModule.rid ℚ ℂ ℂ).injective
      (by simpa only [map_zero] using ha)
  · intro w
    rw [g32c_gammaAbs_prodAbs]
    rw [g32c_class_cross X S hS (2 * q) (2 * e) (2 * c) hce w z,
      g32c_contraction_crossC A.X (g32c_B X S hS) d hB I c p q e h hce hed]
    rw [← g32c_classB_mul X S hS (2 * e) (2 * p) (2 * d) hed z yy, hmul]

end HodgeLean.Foundations.Program
