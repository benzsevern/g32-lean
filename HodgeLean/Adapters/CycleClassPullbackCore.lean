import HodgeLean.Adapters.AbelianCMData
import HodgeLean.Adapters.AbelianPower
import HodgeLean.Adapters.AbelianHomPullbackDegrees
import HodgeLean.Adapters.CycleClassScope
import HodgeLean.Adapters.CycleClassPullbackDefs
import HodgeLean.Adapters.DegreeZeroUnconditional

/-! # Algebraic pullback along powers sum maps: independent core -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

variable {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
  {L : Type*} [Field L] [Algebra ℚ L] {r : ℕ}

theorem ccm2_ComponentCycle_class_mem_aux {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {q : ℕ} (c : ccm2_ComponentCycle X q) :
    c.class ∈ algebraicCycleClassSpan X q := by
  classical
  unfold ccm2_ComponentCycle.class
  apply Submodule.sum_mem
  intro x hx
  apply Submodule.smul_mem
  unfold algebraicCycleClassSpan
  apply le_sSup (s := {Submodule.span ℚ {cycleComponentSheafClass X y hy} |
    (y : X.left) (hy : Order.coheight y = q)})
  exact ⟨x.1, x.2, rfl⟩
  exact Submodule.subset_span (Set.mem_singleton _)

theorem ccm2_ComponentCycle_class_add_aux {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {q : ℕ} (c d : ccm2_ComponentCycle X q) :
    (c + d).class = c.class + d.class := by
  classical
  unfold ccm2_ComponentCycle.class
  let f : ccm2_CodimensionPoint X q → ℚ → HQ X (2 * q) :=
    fun x m ↦ m • cycleComponentSheafClass X x.1 x.2
  change (c + d).sum f = c.sum f + d.sum f
  apply Finsupp.sum_add_index'
  · intro x
    dsimp [f]
    exact zero_smul ℚ _
  · intro x m n
    dsimp [f]
    exact add_smul m n _

theorem ccm2_ComponentCycle_class_smul_aux {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {q : ℕ} (m : ℚ) (c : ccm2_ComponentCycle X q) :
    (m • c).class = m • c.class := by
  classical
  unfold ccm2_ComponentCycle.class
  let v : ccm2_CodimensionPoint X q → HQ X (2 * q) :=
    fun x ↦ cycleComponentSheafClass X x.1 x.2
  let f : ccm2_CodimensionPoint X q → ℚ → HQ X (2 * q) :=
    fun x n ↦ n • v x
  change (m • c).sum f = m • c.sum f
  rw [Finsupp.sum_smul_index', Finsupp.smul_sum]
  · congr 1
    funext x n
    dsimp [f]
    exact mul_smul m n (v x)
  · intro x
    dsimp [f]
    exact zero_smul ℚ _

theorem ccm2_exists_ne_zero_coordinate_aux (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (a : Fin r → pwOrder A θ) (ha : a ≠ 0) :
    ∃ i, a i ≠ 0 := by
  contrapose! ha
  funext i
  exact ha i

theorem ccm2_theta_isUnit_of_ne_zero_aux (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (b : pwOrder A θ) (hb : b ≠ 0) : IsUnit (θ (b : L)) := by
  exact (isUnit_iff_ne_zero.mpr (Subtype.coe_ne_coe.mpr hb)).map θ

private theorem ccm2_finite_pow_kernel (n : ℕ) (hn : 0 < n) :
    Set.Finite {x : ComplexPoint A | x ^ n = 1} := by
  let e := HodgeLean.Foundations.complexPointUniformization A (TopologicalSpace.dim A.left)
  have hc := AddCircle.finite_torsion (1 : ℝ) hn
  have ht : (Set.univ.pi fun _ : Fin (2 * TopologicalSpace.dim A.left) =>
      {x : UnitAddCircle | n • x = 0}).Finite := Set.Finite.pi fun _ => hc
  refine Set.Finite.of_injOn (f := fun x : ComplexPoint A => e (Additive.ofMul x))
    ?_ (e.injective.comp Additive.ofMul.injective).injOn ht
  intro x hx i _
  have h : n • e (Additive.ofMul x) = 0 := by
    rw [← map_nsmul]
    change e (Additive.ofMul (x ^ n)) = 0
    rw [hx]
    exact map_zero e
  exact congrFun h i

omit [IsCommMonObj A] in
private theorem ccm2_surjective_pow (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun x : ComplexPoint A => x ^ n) := by
  let e := HodgeLean.Foundations.complexPointUniformization A (TopologicalSpace.dim A.left)
  intro x
  have h : ∀ i, ∃ y : UnitAddCircle, n • y = e (Additive.ofMul x) i :=
    fun i => by
      obtain ⟨y, hy⟩ := DivisibleBy.surjective_smul UnitAddCircle ℤ (Int.natCast_ne_zero.mpr hn.ne') (e (Additive.ofMul x) i)
      exact ⟨y, by simpa only [natCast_zsmul] using hy⟩
  choose y hy using h
  refine ⟨(e.symm y).toMul, ?_⟩
  apply Additive.ofMul.injective
  apply e.injective
  change e (n • e.symm y) = e (Additive.ofMul x)
  rw [map_nsmul, e.apply_symm_apply]
  exact funext hy

open scoped TensorProduct

omit [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] in
private theorem ccm2_natCast_points (n : ℕ) (x : ComplexPoint A) :
    Point.map (n : AbelianEnd A).hom x = x ^ n := by
  have h : (n : AbelianEnd A).hom = 𝟙 A ^ n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change ((n : AbelianEnd A) + 1).hom = _
      rw [AbelianEnd.add_hom, ih, pow_succ, AbelianEnd.one_hom]
  change x ≫ (n : AbelianEnd A).hom = _
  rw [h, MonObj.comp_pow, Category.comp_id]

private theorem ccm2_includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight :
      AbelianEnd A →ₐ[ℤ] AbelianEnd0 A) := by
  intro f g h
  have h' := congrArg (abelianEnd0Action A) h
  change abelianEnd0Action A ((1 : ℚ) ⊗ₜ[ℤ] f) =
    abelianEnd0Action A ((1 : ℚ) ⊗ₜ[ℤ] g) at h'
  rw [spec_g4_abelianEnd0Action_tmul, spec_g4_abelianEnd0Action_tmul,
    one_smul, one_smul] at h'
  exact spec_abelianEndAction_injective A (MulOpposite.op_injective h')

private theorem ccm2_inverse_multiple {L : Type*} [Field L] [Algebra ℚ L]
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (b : pwOrder A θ) (hb : b ≠ 0) :
    ∃ (n : ℕ) (g : AbelianEnd A), 0 < n ∧
      g * pwOrderEnd A θ b = n ∧ pwOrderEnd A θ b * g = n := by
  obtain ⟨n, hn, hc⟩ := spec_g4_exists_nat_mul_mem_pwOrder A θ (b : L)⁻¹
  let c : pwOrder A θ := ⟨(n : L) * (b : L)⁻¹, hc⟩
  let j : AbelianEnd A →ₐ[ℤ] AbelianEnd0 A := Algebra.TensorProduct.includeRight
  have hf : j (pwOrderEnd A θ b) = θ (b : L) :=
    (spec_g4_tmul_eq_iff_pwOrderEnd A θ b _).mpr rfl
  have hg : j (pwOrderEnd A θ c) = θ ((n : L) * (b : L)⁻¹) :=
    (spec_g4_tmul_eq_iff_pwOrderEnd A θ c _).mpr rfl
  have hb' : (b : L) ≠ 0 := Subtype.coe_ne_coe.mpr hb
  refine ⟨n, pwOrderEnd A θ c, hn, ?_, ?_⟩
  · apply ccm2_includeRight_injective
    change j (_ * _) = j (n : AbelianEnd A)
    rw [map_mul, hf, hg, ← map_mul, mul_assoc, inv_mul_cancel₀ hb', mul_one,
      map_natCast, map_natCast]
  · apply ccm2_includeRight_injective
    change j (_ * _) = j (n : AbelianEnd A)
    rw [map_mul, hf, hg, ← map_mul, mul_left_comm, mul_inv_cancel₀ hb', mul_one,
      map_natCast, map_natCast]

theorem ccm2_pwOrderEnd_isogeny_of_ne_zero_aux (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (b : pwOrder A θ) (hb : b ≠ 0) :
    ccm2_IsogenyOnPoints (pwOrderEnd A θ b).hom := by
  obtain ⟨n, g, hn, hgf, hfg⟩ := ccm2_inverse_multiple θ b hb
  constructor
  · apply (ccm2_finite_pow_kernel (A := A) n hn).subset
    intro x hx
    change Point.map (pwOrderEnd A θ b).hom x = 1 at hx
    change x ^ n = 1
    rw [← ccm2_natCast_points, ← hgf]
    change (x ≫ (pwOrderEnd A θ b).hom ≫ g.hom) = 1
    rw [← Category.assoc]
    change Point.map g.hom (Point.map (pwOrderEnd A θ b).hom x) = 1
    rw [hx]
    exact MonObj.one_comp g.hom
  · intro x
    obtain ⟨y, hy⟩ := ccm2_surjective_pow (A := A) n hn x
    refine ⟨Point.map g.hom y, ?_⟩
    change (y ≫ g.hom) ≫ (pwOrderEnd A θ b).hom = x
    rw [Category.assoc]
    change Point.map (pwOrderEnd A θ b * g).hom y = x
    rw [hfg, ccm2_natCast_points]
    exact hy

theorem ccm2_incl_pwSumMap_aux (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (i : Fin r) :
    P.incl i ≫ P.pwSumMap θ a = (pwOrderEnd A θ (a i)).hom := by
  classical
  rw [AbelianPowerData.pwSumMap, AbelianPowerData.sumMap]
  have hcomp (s : Finset (Fin r)) :
      P.incl i ≫ ∏ j ∈ s, (P.proj j ≫ (pwOrderEnd A θ (a j)).hom) =
        ∏ j ∈ s, P.incl i ≫ (P.proj j ≫ (pwOrderEnd A θ (a j)).hom) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        rw [Finset.prod_insert hj, Finset.prod_insert hj, MonObj.comp_mul, ih]
  rw [hcomp Finset.univ]
  simp only [← Category.assoc, P.incl_proj]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    rw [ite_eq_right (Ne.symm hji), MonObj.one_comp]
  · simp

theorem ccm2_pwSumMap_surjective_of_ne_zero_aux (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (ha : a ≠ 0) :
    Function.Surjective (Point.map (P.pwSumMap θ a)) := by
  obtain ⟨i, hi⟩ := ccm2_exists_ne_zero_coordinate_aux θ a ha
  intro x
  obtain ⟨z, hz⟩ := (ccm2_pwOrderEnd_isogeny_of_ne_zero_aux θ (a i) hi).2 x
  refine ⟨Point.map (P.incl i) z, ?_⟩
  rw [← hz, ← ccm2_incl_pwSumMap_aux P θ a i]
  rfl

theorem ccm2_pwSumMap_ne_one_of_ne_zero_aux (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (ha : a ≠ 0)
    (hA : ∃ x : ComplexPoint A, x ≠ 1) :
    P.pwSumMap θ a ≠ 1 := by
  intro hmap
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hy⟩ := ccm2_pwSumMap_surjective_of_ne_zero_aux P θ a ha x
  apply hx
  rw [← hy, hmap]
  exact MonObj.comp_one y

theorem ccm2_homPullback_span_of_component_cycles_aux (f : Y ⟶ A) (q : ℕ)
    (hcomponent : ∀ (x : A.left) (hx : Order.coheight x = q),
      ∃ c : ccm2_ComponentCycle Y q,
        homPullback f (2 * q) (cycleComponentSheafClass A x hx) = c.class) :
    (algebraicCycleClassSpan A q).map (homPullback f (2 * q)) ≤
      algebraicCycleClassSpan Y q := by
  apply Submodule.map_le_iff_le_comap.mpr
  rw [algebraicCycleClassSpan]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  change homPullback f (2 * q) (cycleComponentSheafClass A x hx) ∈
    algebraicCycleClassSpan Y q
  obtain ⟨c, hc⟩ := hcomponent x hx
  rw [hc]
  exact ccm2_ComponentCycle_class_mem_aux c

theorem ccm2_pwSumMap_zero_aux (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) : P.pwSumMap θ 0 = 1 := by
  have hz : pwOrderEnd A θ (0 : pwOrder A θ) = 0 :=
    ((spec_g4_tmul_eq_iff_pwOrderEnd A θ (0 : pwOrder A θ) 0).mp (by simp)).symm
  simp [AbelianPowerData.pwSumMap, AbelianPowerData.sumMap, hz]

theorem ccm2_homPullback_one_span_aux (q : ℕ) :
    (algebraicCycleClassSpan A q).map (homPullback (1 : Y ⟶ A) (2 * q)) ≤
      algebraicCycleClassSpan Y q := by
  by_cases hq : q = 0
  · subst q
    have ht : algebraicCycleClassSpan Y 0 = ⊤ :=
      algebraicCycleClassSpan_zero_eq_top_unconditional Y
    rw [ht]
    intro x hx
    trivial
  · have hpos : 1 ≤ 2 * q := by omega
    have hzero : homPullback (1 : Y ⟶ A) (2 * q) = 0 := by
      have h := spec_homPullback_zpow_degree (1 : Y ⟶ A) 0 (2 * q)
      rw [zpow_zero, Int.cast_zero, zero_pow (by omega), zero_smul] at h
      exact h
    rintro _ ⟨a, ha, rfl⟩
    rw [hzero, LinearMap.zero_apply]
    exact Submodule.zero_mem _

theorem ccm2_pwSumMap_zero_span_aux (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (q : ℕ) :
    (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ 0) (2 * q)) ≤
      algebraicCycleClassSpan Y q := by
  rw [ccm2_pwSumMap_zero_aux P θ]
  exact ccm2_homPullback_one_span_aux q

theorem ccm2_pwSumMap_codimension_zero_aux (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) :
    (algebraicCycleClassSpan A 0).map (homPullback (P.pwSumMap θ a) 0) ≤
      algebraicCycleClassSpan Y 0 := by
  have ht : algebraicCycleClassSpan Y 0 = ⊤ :=
    algebraicCycleClassSpan_zero_eq_top_unconditional Y
  rw [ht]
  intro x hx
  trivial

theorem ccm2_hPull_of_zero_or_nonzero_aux (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (hnz : ∀ (a : Fin r → pwOrder A θ), a ≠ 0 → ∀ q : ℕ,
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q) :
    ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q := by
  intro a q
  by_cases ha : a = 0
  · subst a
    exact ccm2_pwSumMap_zero_span_aux P θ q
  · exact hnz a ha q

end HodgeLean.Adapters
