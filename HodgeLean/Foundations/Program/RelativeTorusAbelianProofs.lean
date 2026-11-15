import HodgeLean.Foundations.Program.RelativeTorusAbelianHolomorphic

set_option maxHeartbeats 400000

/-! # Track B2, comparison with the complex points of an abelian variety: proofs

One `_aux` theorem per statement of the frozen `RelativeTorusAbelian.lean`.
* Hodge filtration: `H^{1,0}` is the lattice-side holomorphic piece
  (`spec_g4_cohomologyHodgePiece_one_eq`); the pairing with a holomorphic class is its
  complex-linear functional applied to the evaluation, and coordinate functionals all occur
  (`spec_complexAbelianPeriod_restriction`).
* Weight one and dimension: every vector is `r x + i r y` for the real lift `r`
  (`RelativeTorusAbelianLattice.lean`); `F = {r (i v) - i r v}` and `F̄ = {r (i v) + i r v}`.
* Comparison: `exp ∘ eval` has kernel the lattice image; holomorphy in the torus charts
  (`RelativeTorusAbelianHolomorphic.lean`), with the inverse from the holomorphic local inverse of
  the exponential in the identity chart.
* Riemann forms: `H(v, w) = (-i / 2) Q_ℂ(conj (f w), f v)` for `f v = r (i v) - i r v`, and
  conversely `Q_ℂ(r a, r b) = Im H(a, b)`; nondegeneracy through `latticeClassHQ` and the
  exterior square of the period equivalence.
* Endomorphisms: `eval ∘ φ_ℂ = A_f ∘ eval` (`spec_latticeRepresentation_eq_analytic`).
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Manifold
open scoped TensorProduct ContDiff CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open HodgeLean.Foundations.AppellHumbert

namespace HodgeLean.Foundations.Program

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- A complex-linear real functional is complex homogeneous. -/
theorem b2a_holomorphic_smul {g : ℕ} {f : DegreeOneLatticeDual g}
    (hf : f ∈ degreeOneLatticeHolomorphic g) (c : ℂ) (v : Fin g → ℂ) : f (c • v) = c * f v := by
  have hc : c • v = c.re • v + c.im • (Complex.I • v) := by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
  rw [hc, map_add, map_smul, map_smul, hf v, Complex.real_smul, Complex.real_smul, ← mul_assoc,
    ← add_mul, Complex.re_add_im]

/-- The period pairing against `d ⊗ λ` is `d` times the complexified period. -/
theorem b2a_pairing_tmul (ξ : ℂ ⊗[ℚ] HQ X 1) (d : ℂ) (l : b2_abelianLattice X) :
    b2_abelianPairing X ξ (d ⊗ₜ l) = d * complexAbelianPeriod X ξ l := by
  induction ξ using TensorProduct.inductionOn with
  | tmul c x =>
    simp only [b2_abelianPairing, b2_abelianPeriodDual, complexAbelianPeriod,
      LinearMap.liftBaseChange_tmul, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk,
      smul_eq_mul, TensorProduct.AlgebraTensorModule.lift_tmul, LinearMap.toSpanSingleton_apply,
      LinearMap.coe_comp, Function.comp_apply, Pi.smul_apply, LinearMap.compLeft_apply,
      Algebra.linearMap_apply, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, abelianPeriodEquiv]
    rw [Classical.choose_spec (spec_abelianPeriod_equiv X) x l]
    simp only [eq_ratCast]
    ring
  | add ξ ξ' h h' => rw [map_add, LinearMap.add_apply, h, h', map_add, Pi.add_apply, mul_add]

/-- For a holomorphic class, the pairing is its functional applied to the evaluation. -/
theorem b2a_pairing_eq_eval (ξ : ℂ ⊗[ℚ] HQ X 1) (f : DegreeOneLatticeDual (dim X.left))
    (hf : f ∈ degreeOneLatticeHolomorphic (dim X.left))
    (hξ : latticeRestriction X f = complexAbelianPeriod X ξ) (u : ℂ ⊗[ℤ] b2_abelianLattice X) :
    b2_abelianPairing X ξ u = f (b2_abelianEval X u) := by
  induction u using TensorProduct.inductionOn with
  | tmul d l =>
    rw [b2a_pairing_tmul, b2a_eval_tmul, b2a_holomorphic_smul hf, ← hξ]
    rfl
  | add u w hu hw => rw [map_add, hu, hw, map_add, map_add]

theorem b2_abelianHodgeF_eq_aux : b2_abelianHodgeF X = b2_abelianF X := by
  let := (finiteBetti_abelian X).finite 1
  have hH : (abelianWeightOneHodgeStructure X).H (1, 0) = complexHolomorphicH1 X := by
    change cohomologyHodgePiece X 1 (1, 0) = _
    rw [spec_g4_cohomologyHodgePiece_one_eq X]
    simp [latticeHodgePieces]
  ext u
  rw [b2_abelianHodgeF, Submodule.mem_dualCoannihilator, hH]
  constructor
  · intro hu
    obtain ⟨Φ, hΦ⟩ := spec_complexAbelianPeriod_restriction X
    change b2_abelianEval X u = 0
    funext i
    let fi : DegreeOneLatticeDual (dim X.left) :=
      (LinearMap.proj i : (Fin (dim X.left) → ℂ) →ₗ[ℂ] ℂ).restrictScalars ℝ
    have hfi : fi ∈ degreeOneLatticeHolomorphic (dim X.left) := fun v ↦ by
      simp [fi]
    have hξ : latticeRestriction X fi = complexAbelianPeriod X (Φ.symm fi) := by
      rw [← hΦ, LinearEquiv.apply_symm_apply]
    have := hu _ (Submodule.mem_map_of_mem (f := b2_abelianPairing X)
      (show Φ.symm fi ∈ complexHolomorphicH1 X from ⟨fi, hfi, hξ⟩))
    rw [b2a_pairing_eq_eval X _ fi hfi hξ] at this
    simpa [fi] using this
  · intro hu φ hφ
    obtain ⟨ξ, ⟨f, hf, hξ⟩, rfl⟩ := Submodule.mem_map.1 hφ
    rw [b2a_pairing_eq_eval X ξ f hf hξ, show b2_abelianEval X u = 0 from hu, map_zero]

theorem b2_abelianF_isWeightOne_aux : b2_IsWeightOne (b2_abelianLattice X) (b2_abelianF X) := by
  rw [b2_IsWeightOne, b2a_conjSubmodule_eq]
  constructor
  · rw [Submodule.disjoint_def]
    rintro u hu ⟨w, hw, rfl⟩
    obtain ⟨b, rfl⟩ := (b2a_mem_F_iff X w).1 hw
    change b2_abelianEval X (b2_conj _ (b2a_f X b)) = 0 at hu
    rw [b2a_conj_f, map_add, LinearMap.map_smul, b2a_eval_lift, b2a_eval_lift] at hu
    have hb : b = 0 := by
      have h2 : (2 * Complex.I) • b = 0 := by rw [two_mul, add_smul]; exact hu
      exact (smul_eq_zero.1 h2).resolve_left (by simp)
    subst hb
    change b2_conj _ (b2a_f X 0) = 0
    rw [b2a_f, smul_zero, map_zero, smul_zero, sub_zero, map_zero]
  · rw [codisjoint_iff_le_sup]
    intro u _
    obtain ⟨x, y, rfl⟩ := b2a_decomp X u
    set a : Fin (dim X.left) → ℂ := (2⁻¹ : ℂ) • (-(Complex.I • x) - y)
    set b : Fin (dim X.left) → ℂ := (2⁻¹ : ℂ) • (y - Complex.I • x)
    have hab : Complex.I • a + Complex.I • b = x := by
      funext i
      simp only [a, b, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
      linear_combination (-(x i)) * Complex.I_sq
    have hba : b - a = y := by
      funext i
      simp only [a, b, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
    refine Submodule.mem_sup.2 ⟨b2a_f X a, b2a_f_mem X a, b2_conj _ (b2a_f X b),
      ⟨b2a_f X b, b2a_f_mem X b, rfl⟩, ?_⟩
    rw [b2a_conj_f, b2a_f, ← hab, ← hba, map_add, map_sub, smul_sub]
    abel

theorem b2_abelian_finrank_aux :
    Module.finrank ℂ ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X) = dim X.left :=
  ((b2_abelianEval X).quotKerEquivOfSurjective (b2a_eval_surjective X)).finrank_eq.trans
    (Module.finrank_fin_fun ℂ)

theorem b2a_toPoint_mk (v : ℂ ⊗[ℤ] b2_abelianLattice X) :
    b2_abelianToPoint X (QuotientAddGroup.mk (Submodule.Quotient.mk v)) =
      complexExponential X (dim X.left) (b2_abelianEval X v) := rfl

theorem b2_abelianToPoint_bijective_aux : Function.Bijective (b2_abelianToPoint X) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    induction t using QuotientAddGroup.induction_on with
    | H q =>
    induction q using Submodule.Quotient.induction_on with
    | H v =>
    rw [b2a_toPoint_mk] at ht
    let l : b2_abelianLattice X := ⟨b2_abelianEval X v, ht⟩
    refine (QuotientAddGroup.eq_zero_iff _).2 ⟨l, ?_⟩
    change Submodule.Quotient.mk ((1 : ℂ) ⊗ₜ[ℤ] l) = Submodule.Quotient.mk v
    rw [Submodule.Quotient.eq]
    change b2_abelianEval X _ = 0
    rw [map_sub, b2a_eval_tmul, one_smul, sub_eq_zero]
  · intro x
    obtain ⟨v, hv⟩ := surjective_complexExponential X (dim X.left) x
    exact ⟨QuotientAddGroup.mk (Submodule.Quotient.mk (b2a_lift X v)), by
      rw [b2a_toPoint_mk, b2a_eval_lift, hv]⟩

theorem b2_abelianToPoint_contMDiff_aux :
    haveI := b2_latticeMap_discrete (b2_abelianF X) (b2_abelianF_isWeightOne_aux X)
    ContMDiff
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X)) → ℂ)
      𝓘(ℂ, Fin (dim X.left) → ℂ) ω (fun t ↦ Additive.toMul (b2_abelianToPoint X t)) :=
  haveI := b2_latticeMap_discrete (b2_abelianF X) (b2_abelianF_isWeightOne_aux X)
  b2a_toPoint_contMDiff X

theorem b2_abelianToPoint_symm_contMDiff_aux :
    haveI := b2_latticeMap_discrete (b2_abelianF X) (b2_abelianF_isWeightOne_aux X)
    ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X)) → ℂ) ω
      (fun x : ComplexPoint X ↦
        (Equiv.ofBijective _ (b2_abelianToPoint_bijective_aux X)).symm (Additive.ofMul x)) :=
  haveI := b2_latticeMap_discrete (b2_abelianF X) (b2_abelianF_isWeightOne_aux X)
  b2a_toPoint_symm_contMDiff X (b2_abelianToPoint_bijective_aux X)

theorem b2_abelian_isRiemannForm_iff_aux (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X)) :
    b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q ↔
      ∃ H : HermitianForm (V := Fin (dim X.left) → ℂ), H.IsPositiveDefinite ∧
        ∀ l m : b2_abelianLattice X, (Q l m : ℝ) = H.imaginary l m := by
  constructor
  · intro hQ
    exact ⟨b2a_hermitian X Q hQ.alt, b2a_hermitian_pos X Q hQ, b2a_hermitian_im X Q hQ⟩
  · rintro ⟨H, hH, hE⟩
    exact b2a_isRiemannForm_of_hermitian X Q H hH hE

theorem b2_abelian_nondegenerate_aux (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    Symplectic.IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X)
      (latticeClassHQ X (b2_bilinToAddHom Q))) := by
  obtain ⟨H, hH, hE⟩ := (b2_abelian_isRiemannForm_iff_aux X Q).1 hQ
  have hnd := latticeClassHQ_latticeClass_nondegenerate (abelianPeriodLattice X) H hH
    (b2_bilinToAddHom Q) hE
  have hsymm : polarizationVec (torusCohomology_cupProductOf X)
      (latticeClassHQ X (b2_bilinToAddHom Q)) =
      exteriorPower.map 2 (abelianPeriodEquiv X).symm.toLinearMap
        (latticeClass (b2_bilinToAddHom Q)) :=
    ((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm_apply_apply _
  rw [hsymm]
  exact b2a_isNondegenerate_map (abelianPeriodEquiv X).symm hnd

/-- `eval ∘ φ_ℂ = A_f ∘ eval` for the lattice map `φ` of `f` and its analytic representation. -/
theorem b2a_eval_cplxMap [IsCommMonObj X] (f : AbelianEnd X)
    (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l))
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)))
    (u : ℂ ⊗[ℤ] b2_abelianLattice X) :
    b2_abelianEval X (b2_cplxMap φ u) = A (b2_abelianEval X u) := by
  induction u using TensorProduct.inductionOn with
  | tmul c l =>
    change b2_abelianEval X (c ⊗ₜ φ l) = _
    rw [b2a_eval_tmul, b2a_eval_tmul, map_smul,
      spec_latticeRepresentation_eq_analytic X f A hA φ hφ l]
  | add u w hu hw => rw [map_add, map_add, hu, hw, map_add, map_add]

theorem b2_abelianEnd_preserves_aux (f : AbelianEnd X)
    (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l)) :
    b2_abelianF X ≤ (b2_abelianF X).comap (b2_cplxMap φ) := by
  intro u hu
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  obtain ⟨A, hA⟩ := spec_abelianEnd_analyticRepresentation X f
  rw [Submodule.mem_comap]
  change b2_abelianEval X _ = 0
  rw [b2a_eval_cplxMap X f φ hφ A hA, show b2_abelianEval X u = 0 from hu, map_zero]

theorem b2_abelianEnd_torusHom_aux (f : AbelianEnd X)
    (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l))
    (hφF : b2_abelianF X ≤ (b2_abelianF X).comap (b2_cplxMap φ))
    (t : b2_torus (b2_abelianLattice X) (b2_abelianF X)) :
    Additive.toMul (b2_abelianToPoint X (b2_torusHom _ _ φ hφF t)) =
      Point.map f.hom (Additive.toMul (b2_abelianToPoint X t)) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  obtain ⟨A, hA⟩ := spec_abelianEnd_analyticRepresentation X f
  induction t using QuotientAddGroup.induction_on with
  | H q =>
  induction q using Submodule.Quotient.induction_on with
  | H v =>
  change Additive.toMul (b2_abelianToPoint X
    (QuotientAddGroup.mk (Submodule.Quotient.mk (b2_cplxMap φ v)))) = _
  rw [b2a_toPoint_mk, b2a_toPoint_mk, b2a_eval_cplxMap X f φ hφ A hA, hA]

end HodgeLean.Foundations.Program
