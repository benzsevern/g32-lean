import HodgeLean.Adapters.CycleClassDivisorPowersDefs
import HodgeLean.Foundations.CMCentreInvariantsProofs

/-! # Top-degree divisor-power proof obligations

The top-degree route uses a closed point and the top cohomology line.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 2048
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Curves
namespace HodgeLean.Adapters

open scoped CategoryTheory.MonObj in
/-- Source: Hatcher, Algebraic Topology, Theorem 3.26; Fulton,
Intersection Theory, second edition, §19.1; finrank_HQ_abelian. -/
theorem ccm9_top_cycle_span_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (k : ℕ) (hk : dim X.left = k) :
    algebraicCycleClassSpan X k = ⊤ := by
  letI : SmoothOfRelativeDimension k X.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (X := X.left) (f := X.hom)
    rwa [hk] at h
  letI := (finiteBetti_abelian X).finite (2 * k)
  let z : ComplexPoint X := 1
  let P : X.left := z.underlying
  have hP : IsClosed ({P} : Set X.left) :=
    ((pointEquivClosedPoint X.hom) ⟨z.left, Over.w z⟩).2
  have hPk : Order.coheight P = k := by
    have h := SmoothOfRelativeDimension.height_add_coheight_eq_of_isClosed
      (f := X.hom) (d := k) P hP
    have hmin : IsMin P := by
      intro y hy
      have hy' : y ∈ closure {P} := by
        rwa [← specializes_iff_mem_closure, ← Scheme.le_iff_specializes]
      rw [hP.closure_eq] at hy'
      exact (Set.mem_singleton_iff.mp hy').ge
    rw [Order.IsMin.height_eq_zero hmin, zero_add] at h
    exact_mod_cast h
  obtain ⟨w, hw⟩ := exists_complexFundamentalClass_aux X k
  have hne : cycleComponentSheafClass X P hPk ≠ 0 :=
    cycleComponentSheafClass_ne_zero_of_fundamentalClass X k P hPk w hw
  have hfin : Module.finrank ℚ (HQ X (2 * k)) = 1 := by
    rw [finrank_HQ_abelian, hk]
    exact Nat.choose_self (2 * k)
  have hrank : Module.rank ℚ (HQ X (2 * k)) ≤ 1 := by
    rw [← Module.finrank_eq_rank, hfin]
    norm_num
  have hspan : Submodule.span ℚ {cycleComponentSheafClass X P hPk} = ⊤ :=
    span_singleton_eq_top_of_rank_le_one hrank hne
  apply top_unique
  rw [← hspan]
  apply le_sSup (s := {Submodule.span ℚ {cycleComponentSheafClass X y hy} |
    (y : X.left) (hy : Order.coheight y = k)})
  exact ⟨P, hPk, rfl⟩

/-- Only the top power is asserted; no positivity of the class is required.
Source: Fulton, Intersection Theory, second edition, §19.1;
the top-degree line and its nonzero point class. -/
theorem ccm9_polarization_pow_algebraic_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (η : HQ X 2) (k : ℕ) (hk : dim X.left = k) :
    cupPow X (cupProductOf X) η k ∈ algebraicCycleClassSpan X k := by
  rw [ccm9_top_cycle_span_aux X k hk]
  exact (Submodule.mem_top :
    cupPow X (cupProductOf X) η k ∈ (⊤ : Submodule ℚ (HQ X (2 * k))))

/-- The product of the two point polarizations has nonzero square.
Source: Birkenhake--Lange, Complex Abelian Varieties, second edition,
§1.3 and §4.1; the exterior algebra of the direct sum of two rank-two spaces. -/
theorem ccm9_theta_square_ne_zero_aux :
    cupPow (g3_power E 2) (cupProductOf (g3_power E 2)) ccm8_thetaClass 2 ≠ 0 := by
  let TE := torusCohomology_cupProductOf E
  let P := g3_powerData E 2
  let TY := torusCohomology_cupProductOf (g3_power E 2)
  let ω : ⋀[ℚ]^2 (HQ E 1) := (TE.cupWedgeEquiv 2).symm ccm8_pointClass
  have hω : ω ≠ 0 := by
    intro h
    apply divisorCycleClass_pointDivisor_ne_zero E cubicInfinity cubicInfinity_isClosed
    change ccm8_pointClass = 0
    calc
      ccm8_pointClass = TE.cupWedgeEquiv 2 ω :=
        ((TE.cupWedgeEquiv 2).apply_symm_apply ccm8_pointClass).symm
      _ = 0 := by rw [h, map_zero]
  have hdimE : Module.finrank ℚ (HQ E 1) = 2 * 1 := by
    rw [TE.finrank_eq, E_dim]
  have hnd : Symplectic.IsNondegenerate ω :=
    Symplectic.isNondegenerate_of_wedgePow_ne_zero hdimE (by
      simpa [Symplectic.wedgePow_one] using hω)
  obtain ⟨g, b, hg, hb⟩ := Symplectic.exists_basis_sympVec_of_isNondegenerate hnd
  have hg1 : g = 1 := by omega
  subst g
  let e : Fin 2 → HQ (g3_power E 2) 1 := fun i =>
    P.h1Map (b (Sum.inl 0) ⊗ₜ[ℚ] (Pi.single i 1 : Fin 2 → ℚ))
  let f : Fin 2 → HQ (g3_power E 2) 1 := fun i =>
    P.h1Map (b (Sum.inr 0) ⊗ₜ[ℚ] (Pi.single i 1 : Fin 2 → ℚ))
  have he (i : Fin 2) : e i = homPullback (P.proj i) 1 (b (Sum.inl 0)) := by
    fin_cases i <;> simp [e, P, AbelianPowerData.h1Map]
  have hf (i : Fin 2) : f i = homPullback (P.proj i) 1 (b (Sum.inr 0)) := by
    fin_cases i <;> simp [f, P, AbelianPowerData.h1Map]
  have hpull (i : Fin 2) :
      homPullback (P.proj i) 2 ccm8_pointClass =
        TY.cupWedgeEquiv 2 (exteriorPower.ιMulti ℚ 2
          ![homPullback (P.proj i) 1 (b (Sum.inl 0)),
            homPullback (P.proj i) 1 (b (Sum.inr 0))]) := by
    rw [spec_homPullback_eq_cupWedgeEquiv]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show (TE.cupWedgeEquiv 2).symm ccm8_pointClass = ω from rfl, hb]
    simp only [Symplectic.sympVec, Fin.sum_univ_one, Function.comp_apply,
      exteriorPower.map_apply_ιMulti]
    congr 2
  have htheta : (TY.cupWedgeEquiv 2).symm ccm8_thetaClass =
      Symplectic.sympVec e f := by
    apply (TY.cupWedgeEquiv 2).injective
    rw [LinearEquiv.apply_symm_apply, ccm8_thetaClass]
    rw [hpull 0, hpull 1]
    simp only [map_add, Symplectic.sympVec, Fin.sum_univ_two, he, hf]
  have hef : LinearIndependent ℚ (Sum.elim e f) := by
    let h1e : TensorProduct ℚ (HQ E 1) (Fin 2 → ℚ) ≃ₗ[ℚ]
        HQ (g3_power E 2) 1 := LinearEquiv.ofLinearMap P.h1Map P.h1Inv
        (spec_g2_h1Map_comp_h1Inv P) (spec_g2_h1Inv_comp_h1Map P)
    let σ : (Fin 2 ⊕ Fin 2) ≃ ((Fin 1 ⊕ Fin 1) × Fin 2) :=
      { toFun := Sum.elim (fun i => (Sum.inl 0, i)) (fun i => (Sum.inr 0, i))
        invFun := fun p => Sum.elim (fun _ => Sum.inl p.2) (fun _ => Sum.inr p.2) p.1
        left_inv := by intro i; cases i <;> rfl
        right_inv := by
          intro p
          rcases p with ⟨i, j⟩
          cases i with
          | inl x => have hx : x = 0 := Subsingleton.elim _ _; subst x; rfl
          | inr x => have hx : x = 0 := Subsingleton.elim _ _; subst x; rfl }
    let B := ((b.tensorProduct (Pi.basisFun ℚ (Fin 2))).map h1e).reindex σ.symm
    convert B.linearIndependent using 1
    ext i
    cases i with
    | inl i => fin_cases i <;> simp [B, σ, h1e, e, Module.Basis.tensorProduct_apply']
    | inr i => fin_cases i <;> simp [B, σ, h1e, f, Module.Basis.tensorProduct_apply']
  have hpow : Symplectic.wedgePow ((TY.cupWedgeEquiv 2).symm ccm8_thetaClass) 2 ≠ 0 := by
    rw [htheta, Symplectic.wedgePow_sympVec, ← Nat.cast_smul_eq_nsmul ℚ]
    refine smul_ne_zero (by norm_num) ?_
    have hli : LinearIndependent ℚ (Symplectic.interleave e f) :=
      hef.comp (Symplectic.interleaveIdx 2) (Symplectic.interleaveIdx_injective 2)
    exact a4_ιMulti_ne_zero hli
  intro hc
  apply hpow
  apply (TY.cupWedgeEquiv 4).injective
  rw [map_zero]
  exact (cupWedgeEquiv_wedgePow (g3_power E 2) TY ccm8_thetaClass 2).trans hc

end HodgeLean.Adapters
