import HodgeLean.Foundations.Program.TorusAlgebraizationB54ProjGraph
import HodgeLean.Foundations.Program.TorusAlgebraizationB54TranslationCone
import HodgeLean.Foundations.Program.TorusAlgebraizationB54TranslationAction
import HodgeLean.Foundations.Program.TorusAlgebraizationB54TransitiveGraph
import HodgeLean.Foundations.Program.TorusAlgebraizationB54ThetaNormal
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Surjectivity
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Continuity
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Projective
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Presentation
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Domain
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Proj
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Evaluation
import HodgeLean.Foundations.Program.TorusAlgebraizationB52GridMultiplication
import HodgeLean.Foundations.Program.TorusAlgebraizationDefs
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Theta
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Avoidance
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Periodization
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Gaussian
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Hermitian
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Uniform
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Nonzero
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Separation
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Generation
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Addition
import HodgeLean.Foundations.Program.TorusAlgebraizationB52WeightedAddition
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Averaging
import HodgeLean.Foundations.Program.TorusAlgebraizationB52TracedProducts
import HodgeLean.Foundations.Program.TorusAlgebraizationB52ProjectionFormula
import HodgeLean.Foundations.Program.TorusAlgebraizationB52PairedCharacters
import HodgeLean.Foundations.Program.TorusAlgebraizationB52TwistedSpanning
import HodgeLean.Foundations.Program.TorusAlgebraizationB52ThetaRank
import HodgeLean.Foundations.Program.TorusAlgebraizationB52MultiplicationAction
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Tangent
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Points
import HodgeLean.Foundations.Program.TorusAlgebraizationB51Basic
import HodgeLean.Foundations.Program.TorusAlgebraizationB51Refinement
import HodgeLean.Foundations.Program.TorusAlgebraizationB51Sections
import HodgeLean.Foundations.Analytic.Analytification
import HodgeLean.Foundations.Program.RelativeTorusAbelian
import HodgeLean.Foundations.Program.TorusAlgebraizationB55Analytic
import HodgeLean.Foundations.Program.TorusAlgebraizationB55Laws
import HodgeLean.Foundations.Program.TorusAlgebraizationB56Period

noncomputable section
open scoped TensorProduct Pointwise
namespace HodgeLean.Foundations.Program

open BoundedContinuousFunction

theorem b5_hermitian_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z w : b5_V Λ F) :
    star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w := by
  rw [b5_H, b5_H, Complex.star_def, map_mul, ← b2a_baseChange_conj,
    b2v_conj_conj, b2a_baseChange_antisymm Q hQ.alt]
  simp only [map_neg, map_mul, map_ofNat, Complex.conj_I]
  ring

theorem b5_imaginary_lattice_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (l m : Λ) :
    (b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F m)).im = (Q l m : ℝ) := by
  let gl := b5_lift Λ F hF (b5_lattice Λ F l)
  let gm := b5_lift Λ F hF (b5_lattice Λ F m)
  let fl := b2_conj Λ gl
  let fm := b2_conj Λ gm
  have hl : (1 : ℂ) ⊗ₜ[ℤ] l = fl + gl := b5_lift_lattice_decomposition Λ F hF l
  have hm : (1 : ℂ) ⊗ₜ[ℤ] m = fm + gm := b5_lift_lattice_decomposition Λ F hF m
  have hff : Q.baseChange ℂ fl fm = 0 :=
    hQ.isotropic fl (b5_conj_lift_mem Λ F hF _) fm (b5_conj_lift_mem Λ F hF _)
  have hgg : Q.baseChange ℂ gl gm = 0 := by
    calc
      Q.baseChange ℂ gl gm = Q.baseChange ℂ (b2_conj Λ fl) (b2_conj Λ fm) := by
        rw [b2v_conj_conj, b2v_conj_conj]
      _ = star (Q.baseChange ℂ fl fm) := b2a_baseChange_conj Q fl fm
      _ = 0 := by simp [hff]
  have hcross : Q.baseChange ℂ gl fm = star (Q.baseChange ℂ fl gm) := by
    calc
      Q.baseChange ℂ gl fm = Q.baseChange ℂ (b2_conj Λ fl) (b2_conj Λ gm) := by
        rw [b2v_conj_conj]
      _ = star (Q.baseChange ℂ fl gm) := b2a_baseChange_conj Q fl gm
  have hskew : Q.baseChange ℂ fl gm = -Q.baseChange ℂ gm fl :=
    b2a_baseChange_antisymm Q hQ.alt fl gm
  have hQlm : (Q l m : ℂ) =
      -(Q.baseChange ℂ gm fl + star (Q.baseChange ℂ gm fl)) := by
    have hbase : Q.baseChange ℂ ((1 : ℂ) ⊗ₜ[ℤ] l) ((1 : ℂ) ⊗ₜ[ℤ] m) =
        (Q l m : ℂ) := by
      rw [LinearMap.BilinForm.baseChange_tmul]
      simp
    rw [← hbase, hl, hm]
    simp only [map_add, LinearMap.add_apply, hff, hgg, zero_add, add_zero,
      hcross, hskew, star_neg]
    ring
  unfold b5_H
  change (-2 * Complex.I * Q.baseChange ℂ gm fl).im = (Q l m : ℝ)
  calc
    (-2 * Complex.I * Q.baseChange ℂ gm fl).im =
        -2 * (Q.baseChange ℂ gm fl).re := by simp
    _ = (-(Q.baseChange ℂ gm fl + star (Q.baseChange ℂ gm fl))).re := by simp; ring
    _ = ((Q l m : ℂ)).re := congrArg Complex.re hQlm.symm
    _ = (Q l m : ℝ) := by simp

theorem b5_positive_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) (hz : z ≠ 0) :
    0 < (b5_H Λ F hF Q z z).re := by
  have hlift : b5_lift Λ F hF z ≠ 0 := fun h ↦
    hz (b5_lift_injective Λ F hF (h.trans (map_zero _).symm))
  have hconj : b2_conj Λ (b5_lift Λ F hF z) ≠ 0 := fun h ↦
    hlift (by
      calc
        b5_lift Λ F hF z = b2_conj Λ (b2_conj Λ (b5_lift Λ F hF z)) :=
          (b2v_conj_conj _).symm
        _ = b2_conj Λ 0 := congrArg (b2_conj Λ) h
        _ = 0 := map_zero _)
  have hp := hQ.positive (b2_conj Λ (b5_lift Λ F hF z))
    (b5_conj_lift_mem Λ F hF z) hconj
  rw [b5_H, b2a_baseChange_antisymm Q hQ.alt]
  have heq :
      (-2 * Complex.I * -Q.baseChange ℂ (b2_conj Λ (b5_lift Λ F hF z))
        (b5_lift Λ F hF z)).re =
        2 * (Complex.I * Q.baseChange ℂ (b2_conj Λ (b5_lift Λ F hF z))
          (b2_conj Λ (b2_conj Λ (b5_lift Λ F hF z)))).re := by
    rw [b2v_conj_conj]
    have hc : -2 * Complex.I *
        -Q.baseChange ℂ (b2_conj Λ (b5_lift Λ F hF z)) (b5_lift Λ F hF z) =
        (2 : ℂ) * (Complex.I *
          Q.baseChange ℂ (b2_conj Λ (b5_lift Λ F hF z)) (b5_lift Λ F hF z)) := by
      ring
    rw [hc]
    norm_num [Complex.mul_re]
  rw [heq]
  exact mul_pos (by norm_num) hp

theorem b5_semicharacter_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (l m : Λ) :
    b5_chi Λ Q (l + m) = b5_chi Λ Q l * b5_chi Λ Q m * Circle.exp (Real.pi * (Q l m : ℝ)) := by
  obtain ⟨k, hk⟩ := b5_refinement_add_defect_even Λ Q hQ.alt l m
  have href : (b5_refinement Λ Q (l + m) : ℝ) =
      b5_refinement Λ Q l + b5_refinement Λ Q m + (Q l m : ℝ) + 2 * k := by
    exact_mod_cast (by linarith [hk])
  unfold b5_chi
  rw [href]
  have hexp : Circle.exp (Real.pi *
      ((b5_refinement Λ Q l : ℝ) + b5_refinement Λ Q m + (Q l m : ℝ) + 2 * k)) =
      Circle.exp (Real.pi * (b5_refinement Λ Q l : ℝ)) *
        Circle.exp (Real.pi * (b5_refinement Λ Q m : ℝ)) *
        Circle.exp (Real.pi * (Q l m : ℝ)) := by
    rw [mul_add, mul_add, mul_add, Circle.exp_add, Circle.exp_add, Circle.exp_add]
    rw [show Real.pi * (2 * (k : ℝ)) = 2 * Real.pi * k by ring,
      Circle.exp_two_pi_mul_int, mul_one]
  exact hexp

theorem b5_factor_cocycle_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (l m : Λ) (z : b5_V Λ F) :
    b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z := by
  have hsymm : b5_H Λ F hF Q (b5_lattice Λ F m) (b5_lattice Λ F l) =
      star (b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F m)) :=
    (b5_hermitian_aux Λ F hF Q hQ _ _).symm
  have him : (b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F m)).im =
      (Q l m : ℝ) := b5_imaginary_lattice_aux Λ F hF Q hQ l m
  have hleft (x y z : b5_V Λ F) : b5_H Λ F hF Q (x + y) z =
      b5_H Λ F hF Q x z + b5_H Λ F hF Q y z := by
    simp only [b5_H, map_add]
    ring
  have hright (x y z : b5_V Λ F) : b5_H Λ F hF Q x (y + z) =
      b5_H Λ F hF Q x y + b5_H Λ F hF Q x z := by
    simp only [b5_H, map_add, LinearMap.add_apply]
    ring
  unfold b5_factor
  rw [b5_semicharacter_aux Λ F hF Q hQ l m, Circle.coe_mul, Circle.coe_mul,
    Circle.coe_exp]
  rw [map_add, hleft, hright, hleft, hleft, hright]
  generalize (b5_chi Λ Q l : ℂ) = cl
  generalize (b5_chi Λ Q m : ℂ) = cm
  generalize b5_H Λ F hF Q (b5_lattice Λ F l) z = a
  generalize b5_H Λ F hF Q (b5_lattice Λ F m) z = b
  generalize b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F l) = c
  generalize b5_H Λ F hF Q (b5_lattice Λ F m) (b5_lattice Λ F m) = d
  generalize b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F m) = u at hsymm him ⊢
  rw [mul_assoc (cl * cm), ← Complex.exp_add, mul_mul_mul_comm, ← Complex.exp_add]
  congr 2
  apply Complex.ext <;> simp [hsymm, ← him] <;> ring

theorem b5_factor_holomorphic_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (l : Λ) :
    Differentiable ℂ (b5_factor Λ F hF Q l) := by
  let φ : b5_V Λ F →ₗ[ℂ] ℂ :=
    { toFun := fun z ↦ b5_H Λ F hF Q (b5_lattice Λ F l) z
      map_add' := by
        intro z w
        simp only [b5_H, map_add, LinearMap.add_apply]
        ring
      map_smul' := by
        intro c z
        simp only [b5_H, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hd : Differentiable ℂ (fun z ↦ b5_H Λ F hF Q (b5_lattice Λ F l) z) :=
    (LinearMap.toContinuousLinearMap φ).differentiable
  unfold b5_factor
  exact (((hd.const_mul Real.pi).add_const
    ((Real.pi / 2) * b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F l))).cexp).const_mul _

theorem b5_sections_zero_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (f : b5_sections Λ F hF Q 0) :
    ∀ z, f.val z = f.val 0 := by
  classical
  obtain ⟨d, hd⟩ := b5_lattice_real_basis Λ F hF
  let L : Submodule ℤ (b5_V Λ F) := Submodule.span ℤ (Set.range d)
  letI : DiscreteTopology L := inferInstance
  letI : IsZLattice ℝ L := inferInstance
  have hper : ∀ (q : L) (z : b5_V Λ F), f.val (z + q) = f.val z := by
    intro q z
    have hq : (q : b5_V Λ F) ∈ (b5_lattice Λ F).range := by
      rw [← hd]
      exact q.property
    obtain ⟨l, hl⟩ := hq
    have hfe := f.property.2 l z
    rw [pow_zero, one_mul] at hfe
    simpa [hl] using hfe
  have hsec : f.val ∈ HodgeLean.Foundations.AppellHumbert.sections
      (HodgeLean.Foundations.AppellHumbert.Datum.trivial L) := by
    refine ⟨f.property.1, ?_⟩
    intro q z
    rw [hper q z]
    simp [HodgeLean.Foundations.AppellHumbert.holFactor,
      HodgeLean.Foundations.AppellHumbert.Datum.trivial,
      HodgeLean.Foundations.AppellHumbert.HermitianForm.zero]
  obtain ⟨c, hc⟩ :=
    (HodgeLean.Foundations.AppellHumbert.spec_trivial_sections L f.val).mp hsec
  intro z
  rw [hc]

theorem b5_sections_finite_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (n : ℕ) :
    Module.Finite ℂ (b5_sections Λ F hF Q n) := by
  classical
  obtain ⟨d, hd⟩ := b5_lattice_real_basis Λ F hF
  letI : CompactSpace d.parallelepiped :=
    isCompact_iff_compactSpace.mp d.parallelepiped.isCompact
  let Φ := b5_sectionRestriction Λ F hF Q n d
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    apply Subtype.ext
    funext x
    let q := ZSpan.floor d x
    have hq : (q : b5_V Λ F) ∈ (b5_lattice Λ F).range := by
      rw [← hd]
      exact q.property
    obtain ⟨l, hl⟩ := hq
    have hfract : ZSpan.fract d x ∈ d.parallelepiped :=
      ZSpan.fundamentalDomain_subset_parallelepiped d (ZSpan.fract_mem_fundamentalDomain d x)
    have hz : f.val (ZSpan.fract d x) = 0 := by
      have he := congrFun (congrArg DFunLike.coe hf) ⟨ZSpan.fract d x, hfract⟩
      exact he
    have hfe := f.property.2 l (ZSpan.fract d x)
    rw [hl, ZSpan.fract_apply, sub_add_cancel] at hfe
    rw [hfe]
    change _ * f.val (ZSpan.fract d x) = 0
    rw [hz, mul_zero]
  refine b3A_finiteDimensional_of_compact Φ hinj ?_
  let P : Set (b5_V Λ F) := d.parallelepiped
  let K : Set (b5_V Λ F) := P + Metric.closedBall 0 1
  have hK : IsCompact K := by
    simpa [K, P] using d.parallelepiped.isCompact.add (isCompact_closedBall 0 1)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  let A : ℝ := ∑ i, ‖d i‖
  let L : Submodule ℤ (b5_V Λ F) := Submodule.span ℤ (Set.range d)
  letI : DiscreteTopology L := inferInstance
  let T : Set (b5_V Λ F) := Metric.closedBall 0 (R + A) ∩
    (L : Set (b5_V Λ F))
  have hT : T.Finite := by
    apply Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    · exact Metric.isBounded_closedBall
    · exact L.toAddSubgroup.isClosed_of_discreteTopology
  letI : Fintype T := hT.fintype
  have hTl : ∀ q : T, ∃ l : Λ, b5_lattice Λ F l = q := by
    intro q
    have hq : (q : b5_V Λ F) ∈ (b5_lattice Λ F).range := by
      rw [← hd]
      exact q.property.2
    exact hq
  choose l hl using hTl
  have hfactor : ∀ q : T, ∃ M : ℝ, ∀ z ∈ P,
      ‖b5_factor Λ F hF Q (l q) z ^ n‖ ≤ M := by
    intro q
    exact d.parallelepiped.isCompact.exists_bound_of_continuousOn
      (((b5_factor_holomorphic_aux Λ F hF Q hQ (l q)).continuous.pow n).continuousOn)
  choose M hM using hfactor
  let C : ℝ := ∑ q : T, |M q|
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hMC (q : T) : M q ≤ C :=
    (le_abs_self _).trans (by
      simpa [C] using Finset.single_le_sum (f := fun q : T ↦ |M q|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ q))
  have hbound : ∀ (f : b5_sections Λ F hF Q n) (x : b5_V Λ F), x ∈ K →
      ‖f.val x‖ ≤ C * ‖Φ f‖ := by
    intro f x hx
    let q := ZSpan.floor d x
    have hqnorm : ‖(q : b5_V Λ F)‖ ≤ R + A := by
      rw [show (q : b5_V Λ F) = x - ZSpan.fract d x by
        rw [ZSpan.fract_apply, sub_sub_cancel]]
      calc
        ‖x - ZSpan.fract d x‖ ≤ ‖x‖ + ‖ZSpan.fract d x‖ := norm_sub_le _ _
        _ ≤ R + A := add_le_add (mem_closedBall_zero_iff.mp (hR hx))
          (by exact ZSpan.norm_fract_le d x)
    let qt : T := ⟨q, mem_closedBall_zero_iff.mpr hqnorm, q.property⟩
    have hfract : ZSpan.fract d x ∈ P :=
      ZSpan.fundamentalDomain_subset_parallelepiped d (ZSpan.fract_mem_fundamentalDomain d x)
    have hfe := f.property.2 (l qt) (ZSpan.fract d x)
    have hqx : b5_lattice Λ F (l qt) = (q : b5_V Λ F) := hl qt
    rw [hqx, ZSpan.fract_apply, sub_add_cancel] at hfe
    rw [hfe, norm_mul]
    refine mul_le_mul (hM qt _ hfract |>.trans (hMC qt)) ?_ (norm_nonneg _) hC0
    exact (Φ f).norm_coe_le_norm ⟨ZSpan.fract d x, hfract⟩
  intro ρ
  let B : ℝ := C * |ρ|
  have hB0 : 0 ≤ B := mul_nonneg hC0 (abs_nonneg ρ)
  have hderiv (f : b5_sections Λ F hF Q n) (hf : ‖Φ f‖ ≤ ρ)
      (x : b5_V Λ F) (hx : x ∈ P) : ‖fderiv ℂ f.val x‖ ≤ B := by
    apply ContinuousLinearMap.opNorm_le_bound'
    · exact hB0
    intro v hv
    have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    let r : ℝ := 1 / ‖v‖
    have hr : 0 < r := div_pos zero_lt_one hvpos
    let g : ℂ → ℂ := f.val ∘ fun t ↦ x + t • v
    have hline (t : ℂ) : HasDerivAt (fun s : ℂ ↦ x + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have hgdiff : Differentiable ℂ g :=
      f.property.1.comp (fun t ↦ (hline t).differentiableAt)
    have hgder : HasDerivAt g (fderiv ℂ f.val x v) 0 := by
      simpa only [g, Function.comp_apply, zero_smul, add_zero] using
        f.property.1.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 (hline 0)
    have hgB : ∀ t ∈ Metric.sphere (0 : ℂ) r, ‖g t‖ ≤ B := by
      intro t ht
      have htK : x + t • v ∈ K := by
        refine ⟨x, hx, t • v, ?_, rfl⟩
        have htnorm : ‖t‖ = r := by
          simpa only [mem_sphere_zero_iff_norm] using ht
        rw [mem_closedBall_zero_iff, norm_smul, htnorm]
        simp only [r]
        field_simp
        norm_num
      calc
        ‖g t‖ ≤ C * ‖Φ f‖ := hbound f _ htK
        _ ≤ B := by
          exact mul_le_mul_of_nonneg_left (hf.trans (le_abs_self ρ)) hC0
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
      hgdiff.diffContOnCl hgB
    rw [hgder.deriv] at hc
    convert hc using 1 <;> simp [r, div_eq_mul_inv, hv]
  let S : Set (BoundedContinuousFunction d.parallelepiped ℂ) :=
    {g | (∀ x, ‖g x‖ ≤ |ρ|) ∧ ∀ x y, dist (g x) (g y) ≤ B * dist x y}
  refine ⟨closure S, ?_, ?_⟩
  · refine arzela_ascoli (Metric.closedBall (0 : ℂ) |ρ|)
      (isCompact_closedBall 0 |ρ|) S (fun g x hg ↦ ?_) ?_
    · exact mem_closedBall_zero_iff.mpr (hg.1 x)
    · have hlip : ∀ g : S, LipschitzWith (Real.toNNReal B) (g : d.parallelepiped → ℂ) := by
        intro g
        exact LipschitzWith.of_dist_le_mul fun x y ↦ (g.property.2 x y).trans
          (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal B) dist_nonneg)
      exact (LipschitzWith.uniformEquicontinuous _ _ hlip).equicontinuous
  · intro f hf
    apply subset_closure
    refine ⟨fun x ↦ ?_, fun x y ↦ ?_⟩
    · exact ((Φ f).norm_coe_le_norm x).trans (hf.trans (le_abs_self ρ))
    · rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
      exact (convex_parallelepiped d).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ ↦ f.property.1 z) (fun z hz ↦ hderiv f hf z (by simpa [P] using hz))
        y.property x.property

theorem b5_Lcube_basepointFree_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) :
    ∃ s : b5_sections Λ F hF Q 3, s.val z ≠ 0 := by
  obtain ⟨s, hs⟩ := b52_exists_nonzero_section Λ F hF Q
    (b5_hermitian_aux Λ F hF Q hQ)
    (b5_imaginary_lattice_aux Λ F hF Q hQ)
    (b5_positive_aux Λ F hF Q hQ)
    (b5_factor_cocycle_aux Λ F hF Q hQ)
  exact b52_basepoint_of_nonzero_section Λ F hF Q s hs z

theorem b5_Lcube_separatesPoints_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z w : b5_V Λ F) (hzw : ¬ ∃ l : Λ, w = z + b5_lattice Λ F l) :
    ∃ s t : b5_sections Λ F hF Q 3, s.val z * t.val w ≠ s.val w * t.val z := by
  obtain ⟨s, hs⟩ := b52_exists_nonzero_section Λ F hF Q
    (b5_hermitian_aux Λ F hF Q hQ)
    (b5_imaginary_lattice_aux Λ F hF Q hQ)
    (b5_positive_aux Λ F hF Q hQ)
    (b5_factor_cocycle_aux Λ F hF Q hQ)
  have hh : ¬ ∃ l : Λ, w - z = b5_lattice Λ F l := by
    rintro ⟨l, hl⟩
    apply hzw
    refine ⟨l, ?_⟩
    rw [← hl]
    abel
  obtain ⟨u, t, hsep⟩ := b52_points_of_nonzero_section Λ F hF Q
    (b5_hermitian_aux Λ F hF Q hQ) (b5_positive_aux Λ F hF Q hQ)
    s hs z (w - z) hh
  have hw : z + (w - z) = w := by abel
  exact ⟨u, t, by simpa only [hw] using hsep⟩

theorem b5_Lcube_separatesTangents_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z v : b5_V Λ F) (hv : v ≠ 0) :
    ∃ s : b5_sections Λ F hF Q 3, s.val z = 0 ∧ fderiv ℂ s.val z v ≠ 0 := by
  obtain ⟨s, hs⟩ := b52_exists_nonzero_section Λ F hF Q
    (b5_hermitian_aux Λ F hF Q hQ)
    (b5_imaginary_lattice_aux Λ F hF Q hQ)
    (b5_positive_aux Λ F hF Q hQ)
    (b5_factor_cocycle_aux Λ F hF Q hQ)
  exact b52_tangent_of_nonzero_section Λ F hF Q (b5_positive_aux Λ F hF Q hQ)
    s hs z v hv

theorem b54_theta_tangent_injective (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q)
    (z : b5_V Λ F) (t : b5_sections Λ F hF Q 3) (ht : t.val z ≠ 0) :
    Function.Injective (fun v : b5_V Λ F ↦ fun s : b5_sections Λ F hF Q 3 ↦
      t.val z * fderiv ℂ s.val z v - s.val z * fderiv ℂ t.val z v) := by
  intro v w h
  apply sub_eq_zero.mp
  by_contra hn
  obtain ⟨s, hs, hd⟩ := b5_Lcube_separatesTangents_aux Λ F hF Q hQ z (v - w) hn
  apply hd
  rw [map_sub, sub_eq_zero]
  apply mul_left_cancel₀ ht
  simpa only [hs, zero_mul, sub_zero] using congrFun h s

theorem b54_fderiv_section_ratio (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (z : b5_V Λ F)
    (s t : b5_sections Λ F hF Q 3) (ht : t.val z ≠ 0) (v : b5_V Λ F) :
    t.val z ^ 2 * fderiv ℂ (fun x ↦ s.val x / t.val x) z v =
      t.val z * fderiv ℂ s.val z v - s.val z * fderiv ℂ t.val z v := by
  have hd := (s.property.1 z).hasFDerivAt.mul
    ((hasFDerivAt_inv ht).comp z (t.property.1 z).hasFDerivAt)
  have he := congrArg (fun L : b5_V Λ F →L[ℂ] ℂ ↦ L v) hd.fderiv
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul] at he
  change fderiv ℂ (fun x ↦ s.val x * (t.val x)⁻¹) z v =
    s.val z * (fderiv ℂ t.val z v * -(t.val z ^ 2)⁻¹) +
      (t.val z)⁻¹ * fderiv ℂ s.val z v at he
  simp only [div_eq_mul_inv]
  rw [he]
  field_simp
  <;> ring

theorem b54_theta_ratio_tangent_injective (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q)
    (z : b5_V Λ F) (t : b5_sections Λ F hF Q 3) (ht : t.val z ≠ 0) :
    Function.Injective (fun v : b5_V Λ F ↦ fun s : b5_sections Λ F hF Q 3 ↦
      fderiv ℂ (fun x ↦ s.val x / t.val x) z v) := by
  intro v w h
  apply b54_theta_tangent_injective Λ F hF Q hQ z t ht
  funext s
  dsimp only
  rw [← b54_fderiv_section_ratio Λ F hF Q z s t ht v,
    ← b54_fderiv_section_ratio Λ F hF Q z s t ht w]
  exact congrArg (fun c : ℂ ↦ t.val z ^ 2 * c) (congrFun h s)

theorem b5_S_generated_one_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    Algebra.adjoin ℂ (b5_grade Λ F hF Q 1 : Set (b5_S Λ F hF Q)) = ⊤ := by
  apply b52_generated_one_of_multiplication_surjective Λ F hF Q
    (b5_sections_zero_aux Λ F hF Q hQ)
  intro n
  by_cases hn : n = 0
  · subst n
    exact b52_multiplication_zero_surjective Λ F hF Q 1
  letI := b5_sections_finite_aux Λ F hF Q hQ ((3 * (n + 1)) * (n * (n + 1)))
  exact b52_cubic_successive_multiplication_surjective Λ F hF Q
    (b5_hermitian_aux Λ F hF Q hQ)
    (b5_imaginary_lattice_aux Λ F hF Q hQ)
    (b5_factor_cocycle_aux Λ F hF Q hQ)
    (b5_positive_aux Λ F hF Q hQ) n (Nat.pos_of_ne_zero hn)

theorem b54_finite_generators (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    ∃ s : Finset (b5_S Λ F hF Q),
      (∀ x ∈ s, x ∈ b5_grade Λ F hF Q 1) ∧ Algebra.adjoin ℂ (s : Set (b5_S Λ F hF Q)) = ⊤ := by
  letI := b5_sections_finite_aux Λ F hF Q hQ (3 * 1)
  obtain ⟨s, hs⟩ := Submodule.fg_range
    (DirectSum.lof ℂ ℕ (fun n ↦ b5_sections Λ F hF Q (3 * n)) 1)
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    rw [b5_grade, ← hs]
    exact Submodule.subset_span hx
  · apply top_unique
    rw [← b5_S_generated_one_aux Λ F hF Q hQ]
    apply Algebra.adjoin_le
    intro x hx
    apply Algebra.span_le_adjoin ℂ (s : Set (b5_S Λ F hF Q))
    rw [hs]
    exact hx

theorem b54_polynomial_presentation (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    ∃ s : Finset (b5_S Λ F hF Q), (∀ x ∈ s, x ∈ b5_grade Λ F hF Q 1) ∧
      Function.Surjective (MvPolynomial.aeval (R := ℂ) (fun x : s ↦ x.val)) := by
  obtain ⟨s, hs, hgen⟩ := b54_finite_generators Λ F hF Q hQ
  refine ⟨s, hs, ?_⟩
  have hrange : Set.range (fun x : s ↦ x.val) = (s : Set (b5_S Λ F hF Q)) := by
    ext x
    simp
  exact (AlgHom.range_eq_top _).mp (by
    rw [← Algebra.adjoin_range_eq_range_aeval, hrange]
    exact hgen)

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem b54_theta_polynomial_proj_embedding (Λ : Type*) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    (hF : b2_IsWeightOne Λ F) (Q : LinearMap.BilinForm ℤ Λ)
    (hQ : b2_IsRiemannForm Λ F Q) :
    ∃ s : Finset (b5_S Λ F hF Q), ∃ j : b5_X Λ F hF Q ⟶
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule s ℂ),
      AlgebraicGeometry.IsClosedImmersion j := by
  obtain ⟨s, hs, hsurj⟩ := b54_polynomial_presentation Λ F hF Q hQ
  let f := b54_gradedAeval (b5_grade Λ F hF Q) (fun x : s ↦ x.val)
    (fun x ↦ hs x.val x.property)
  exact ⟨s, AlgebraicGeometry.Proj.map f (b54_irrelevant_le_map_of_surjective f hsurj),
    b54_polynomial_proj_immersion _ _ _ hsurj⟩

theorem b54_gradeZero_scalar_bijective (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    Function.Bijective (algebraMap ℂ (b5_grade Λ F hF Q 0)) := by
  letI := b54_S_isDomain Λ F hF Q
  constructor
  · intro c d h
    exact (algebraMap ℂ (b5_S Λ F hF Q)).injective (congrArg Subtype.val h)
  · intro r
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp
      (b52_grade_zero_le_constants Λ F hF Q (b5_sections_zero_aux Λ F hF Q hQ) r.property)
    exact ⟨c, Subtype.ext hc⟩

open CategoryTheory AlgebraicGeometry in
theorem b54_model_proper (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    IsProper (b5_model Λ F hF Q).hom := by
  obtain ⟨s, _, hs⟩ := b54_finite_generators Λ F hF Q hQ
  letI : Algebra.FiniteType ℂ (b5_S Λ F hF Q) := ⟨s, hs⟩
  letI : Algebra.FiniteType (b5_grade Λ F hF Q 0) (b5_S Λ F hF Q) := by
    apply RingHom.finiteType_algebraMap.mp
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (b5_grade Λ F hF Q 0))
    change (algebraMap ℂ (b5_S Λ F hF Q)).FiniteType
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  letI : IsIso (CommRingCat.ofHom (algebraMap ℂ (b5_grade Λ F hF Q 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (b54_gradeZero_scalar_bijective Λ F hF Q hQ)
  change IsProper (Proj.toSpecZero (b5_grade Λ F hF Q) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (b5_grade Λ F hF Q 0))))
  infer_instance

theorem b5_evaluation_irrelevant_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) :
    (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q z) = ⊤ := by
  obtain ⟨s, hs⟩ := b5_Lcube_basepointFree_aux Λ F hF Q hQ z
  let x : b5_S Λ F hF Q := DirectSum.of _ 1 s
  have hxgrade : x ∈ b5_grade Λ F hF Q 1 := ⟨s, rfl⟩
  have hxirr : x ∈ (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ (by omega) hxgrade
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hxirr)
  change IsUnit ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ((b5_eval Λ F hF Q z) x))
  exact IsUnit.map (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    (Ne.isUnit (by simpa [x, b5_eval] using hs))

theorem b54_theta_model_normal (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    AlgebraicGeometry.zmtiso_IsNormal (b5_model Λ F hF Q).left := by
  letI := b5_sections_finite_aux Λ F hF Q hQ 3
  exact b54_theta_model_normal_of_sections Λ F hF Q (Module.finBasis ℂ _)
    (b5_S_generated_one_aux Λ F hF Q hQ)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b5_projective_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    AlgebraicGeometry.IsProjective (b5_model Λ F hF Q).hom := by
  obtain ⟨s, hs, hgen⟩ := b54_finite_generators Λ F hF Q hQ
  have hsgen : Algebra.adjoin ℂ (Set.range (fun x : s ↦ x.val)) = ⊤ := by
    convert hgen using 1
    ext x
    simp
  obtain ⟨v, hv, hgen⟩ := b54_pad_generators (b5_grade Λ F hF Q)
    (fun x : s ↦ x.val) (fun x ↦ hs x.val x.property) hsgen
  apply b54_projective_of_degree_one (b5_grade Λ F hF Q)
    (b54_gradeZero_scalar_bijective Λ F hF Q hQ) (Fintype.card s) v hv
  apply top_unique
  intro x hxTop
  clear hxTop
  have hx : x ∈ Algebra.adjoin ℂ (Set.range v) := by rw [hgen]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap c =>
    exact (Algebra.adjoin (b5_grade Λ F hF Q 0) (Set.range v)).algebraMap_mem
      (algebraMap ℂ (b5_grade Λ F hF Q 0) c)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem b5_integral_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    AlgebraicGeometry.IsIntegral (b5_X Λ F hF Q) := by
  letI := b54_S_isDomain Λ F hF Q
  apply b54_proj_integral_of_domain (b5_grade Λ F hF Q)
  intro h
  obtain ⟨s, hs⟩ := b5_Lcube_basepointFree_aux Λ F hF Q hQ 0
  let x : b5_S Λ F hF Q := DirectSum.of _ 1 s
  have hx : x ∈ (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ (by omega) (show x ∈ b5_grade Λ F hF Q 1 from ⟨s, rfl⟩)
  have hz : x = 0 := h hx
  apply hs
  simpa [x, b5_eval] using congrArg (b5_eval Λ F hF Q 0) hz

open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Analytic
open scoped CategoryTheory.MonObj

/-- The theta map on the universal cover, constructed by evaluation into Proj.
Source: Hartshorne, II.2; Birkenhake–Lange, Theorem 4.5.1. -/
def b5_thetaCoverHom (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) :
    Spec ↧ℂ ⟶ b5_X Λ F hF Q :=
  Proj.fromOfGlobalSections (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q z)
    (b5_evaluation_irrelevant_aux Λ F hF Q hQ z)

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) :
    b5_thetaCoverHom Λ F hF Q hQ z =
      Proj.fromOfGlobalSections (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q z)
        (b5_evaluation_irrelevant_aux Λ F hF Q hQ z) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem b54_thetaCover_over_general (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) :
    b5_thetaCoverHom Λ F hF Q hQ z ≫ (b5_model Λ F hF Q).hom = 𝟙 (Spec ↧ℂ) := by
  change b5_thetaCoverHom Λ F hF Q hQ z ≫
    (Proj.toSpecZero (b5_grade Λ F hF Q) ≫ _) = _
  rw [← Category.assoc, b5_thetaCoverHom, Proj.fromOfGlobalSections_toSpecZero]
  rw [Category.assoc, ← Spec.map_comp]
  have he : (CommRingCat.ofHom (algebraMap ℂ (b5_grade Λ F hF Q 0))) ≫
      CommRingCat.ofHom ((b5_evalGlobal Λ F hF Q z).comp
        (algebraMap (b5_grade Λ F hF Q 0) (b5_S Λ F hF Q))) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv := by
    ext c
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
      (b5_eval Λ F hF Q z (algebraMap ℂ (b5_S Λ F hF Q) c)) =
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c
    congr 1
    letI := b5_sectionsGraded Λ F hF Q 3
    change (DirectSum.coeAlgHom (fun n ↦ b5_sections Λ F hF Q (3 * n)))
      (algebraMap ℂ (b5_S Λ F hF Q) c) z = c
    rw [AlgHom.commutes]
    rfl
  rw [he]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv _

set_option backward.isDefEq.respectTransparency false in
theorem b5_thetaCover_over_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) :
    b5_thetaCoverHom Λ F hF Q hQ z ≫ (b5_model Λ F hF Q).hom = 𝟙 (Spec ↧ℂ) := by
  exact b54_thetaCover_over_general Λ F hF Q hQ z

/-- The complex-valued theta point on the universal cover.
Source: Hartshorne, II.2. -/
def b5_thetaCover (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) : ComplexPoint (b5_model Λ F hF Q) :=
  Over.homMk (b5_thetaCoverHom Λ F hF Q hQ z) (b54_thetaCover_over_general Λ F hF Q hQ z)

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (z : b5_V Λ F) :
    (b5_thetaCover Λ F hF Q hQ z).left = b5_thetaCoverHom Λ F hF Q hQ z := rfl

theorem b54_thetaCover_continuous (Λ : Type) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    (hF : b2_IsWeightOne Λ F) (Q : LinearMap.BilinForm ℤ Λ)
    (hQ : b2_IsRiemannForm Λ F Q) : Continuous (b5_thetaCover Λ F hF Q hQ) := by
  apply b54_continuous_proj_evaluation (b5_grade Λ F hF Q)
    (algebraMap ℂ (b5_grade Λ F hF Q 0)) (b5_eval Λ F hF Q)
    (fun z c ↦ b54_eval_scalar Λ F hF Q z c)
    (b54_eval_continuous Λ F hF Q) _ (b5_evaluation_irrelevant_aux Λ F hF Q hQ)
    (b5_thetaCover Λ F hF Q hQ) (fun _ ↦ rfl)
  intro z
  obtain ⟨s, hs⟩ := b5_Lcube_basepointFree_aux Λ F hF Q hQ z
  refine ⟨1, DirectSum.of _ 1 s, zero_lt_one, ⟨s, rfl⟩, ?_⟩
  simpa [b5_eval] using hs

theorem b54_thetaCover_translate (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q)
    (l : Λ) (z : b5_V Λ F) :
    b5_thetaCover Λ F hF Q hQ z =
      b5_thetaCover Λ F hF Q hQ (z + b5_lattice Λ F l) := by
  apply Over.OverMorphism.ext
  exact b54_eval_proj_translate Λ F hF Q l z _ _

theorem b54_thetaCover_eq_lattice (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q)
    (z w : b5_V Λ F) (h : b5_thetaCover Λ F hF Q hQ z = b5_thetaCover Λ F hF Q hQ w) :
    ∃ l : Λ, w = z + b5_lattice Λ F l := by
  classical
  by_contra hn
  obtain ⟨s, t, hst⟩ := b5_Lcube_separatesPoints_aux Λ F hF Q hQ z w hn
  let r : b5_sections Λ F hF Q 3 := t.val w • s - s.val w • t
  have hrz : r.val z ≠ 0 := by
    change t.val w * s.val z - s.val w * t.val z ≠ 0
    rw [mul_comm (t.val w)]
    exact sub_ne_zero.mpr hst
  have hrw : r.val w = 0 := by
    change t.val w * s.val w - s.val w * t.val w = 0
    ring
  exact b54_eval_proj_ne Λ F hF Q z w _ _ 1 (by omega) (DirectSum.of _ 1 r)
    ⟨r, rfl⟩ (by simpa [b5_eval] using hrz) (by simpa [b5_eval] using hrw)
    (congrArg (fun p : ComplexPoint (b5_model Λ F hF Q) ↦ p.left) h)

theorem b54_thetaCover_add_congr (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q)
    (a z w : b5_V Λ F) (h : b5_thetaCover Λ F hF Q hQ z = b5_thetaCover Λ F hF Q hQ w) :
    b5_thetaCover Λ F hF Q hQ (z + a) = b5_thetaCover Λ F hF Q hQ (w + a) := by
  obtain ⟨l, rfl⟩ := b54_thetaCover_eq_lattice Λ F hF Q hQ z w h
  convert b54_thetaCover_translate Λ F hF Q hQ l (z + a) using 1 <;> congr 1 <;> abel

theorem b54_thetaCover_surjective (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    Function.Surjective (b5_thetaCover Λ F hF Q hQ) := by
  letI := b5_sections_finite_aux Λ F hF Q hQ 3
  intro p
  obtain ⟨z, hz⟩ := b54_proj_point_is_thetaEvaluation Λ F hF Q
    (Module.finrank ℂ (b5_sections Λ F hF Q 3)) (Module.finBasis ℂ _)
    (b5_Lcube_basepointFree_aux Λ F hF Q hQ) (b5_S_generated_one_aux Λ F hF Q hQ)
    (b54_gradeZero_scalar_bijective Λ F hF Q hQ).2
    (b5_evaluation_irrelevant_aux Λ F hF Q hQ) p
  exact ⟨z, Over.OverMorphism.ext hz.symm⟩

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b54_theta_translation_graph (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (a : b5_V Λ F)
    (f : ComplexPoint (b5_model Λ F hF Q) → ComplexPoint (b5_model Λ F hF Q))
    (hf : ∀ z, f (b5_thetaCover Λ F hF Q hQ z) = b5_thetaCover Λ F hF Q hQ (z + a)) :
    ∃ C : Set (HodgeLean.Adapters.gagam_product (b5_model Λ F hF Q) (b5_model Λ F hF Q)).left,
      IsClosed C ∧ HodgeLean.Adapters.gagam_graph _ _ f = Point.underlying ⁻¹' C := by
  letI := b5_sections_finite_aux Λ F hF Q hQ 3
  let b := Module.finBasis ℂ (b5_sections Λ F hF Q 3)
  let v := b54_basisGenerator Λ F hF Q b
  have hv (i) : v i ∈ b5_grade Λ F hF Q 1 := ⟨b i, rfl⟩
  have hg := b54_basis_generates_over_gradeZero Λ F hF Q b
    (b5_S_generated_one_aux Λ F hF Q hQ)
  obtain ⟨m, d, P, hP, hcone⟩ := b54_translation_cone_algebraic Λ F hF Q b a
    (b5_Lcube_basepointFree_aux Λ F hF Q hQ)
  apply b54_proj_graph_carrier (b5_grade Λ F hF Q) (algebraMap ℂ (b5_grade Λ F hF Q 0))
    (b54_gradeZero_scalar_bijective Λ F hF Q hQ).2 v hv hg
    (b5_eval Λ F hF Q) (b54_eval_scalar Λ F hF Q)
    (b5_evaluation_irrelevant_aux Λ F hF Q hQ)
    (b5_thetaCover Λ F hF Q hQ) (fun z => rfl)
    (b54_thetaCover_surjective Λ F hF Q hQ) (fun z => z + a) f hf m P
  intro w
  have he (z : b5_V Λ F) : b54_translationCoordinates Λ F hF Q b a z =
      (fun k => b5_eval Λ F hF Q z (v (finProdFinEquiv.symm k).1) *
        b5_eval Λ F hF Q (z + a) (v (finProdFinEquiv.symm k).2)) := by
    funext k
    simp [b54_translationCoordinates, v, b54_basisGenerator, b5_eval]
  simpa only [he] using hcone w

theorem b5_smooth_aux (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    AlgebraicGeometry.Smooth (b5_model Λ F hF Q).hom := by
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI : IsProjective (b5_model Λ F hF Q).hom := b5_projective_aux Λ F hF Q hQ
  apply b54_smooth_of_transitive_closed_graphs (b5_model Λ F hF Q)
    (b54_theta_model_normal Λ F hF Q hQ)
  intro x y
  let p := b5_thetaCover Λ F hF Q hQ
  let hs := b54_thetaCover_surjective Λ F hF Q hQ
  let hrel := b54_thetaCover_add_congr Λ F hF Q hQ
  obtain ⟨a, ha⟩ := b54_pointTranslation_transitive p hs hrel x y
  refine ⟨b54_pointTranslationEquiv p hs hrel a, ha, ?_, ?_⟩
  · exact b54_theta_translation_graph Λ F hF Q hQ a _
      (b54_pointTranslationEquiv_param p hs hrel a)
  · exact b54_theta_translation_graph Λ F hF Q hQ (-a) _
      (b54_pointTranslationEquiv_symm_param p hs hrel a)

/-- The theta map evaluates at the chosen representative of a torus class.
The subsequent descent identity removes dependence on that representative.
Source: Birkenhake–Lange, Theorem 4.5.1. -/
def b5_theta (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (t : b2_torus Λ F) : ComplexPoint (b5_model Λ F hF Q) :=
  b5_thetaCover Λ F hF Q hQ (b2_coord _ (Quotient.out t))

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (t : b2_torus Λ F) :
    b5_theta Λ F hF Q hQ t = b5_thetaCover Λ F hF Q hQ
      (b2_coord _ (Quotient.out t)) := rfl

theorem b5_theta_descent_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (v : (ℂ ⊗[ℤ] Λ) ⧸ F) :
    b5_theta Λ F hF Q hQ (QuotientAddGroup.mk v) =
      b5_thetaCover Λ F hF Q hQ (b2_coord _ v) := by
  let w := Quotient.out (QuotientAddGroup.mk v : b2_torus Λ F)
  have hw : (QuotientAddGroup.mk w : b2_torus Λ F) = QuotientAddGroup.mk v :=
    Quotient.out_eq _
  obtain ⟨l, hl⟩ := QuotientAddGroup.eq_iff_sub_mem.mp hw
  have hcoord : b2_coord _ w = b2_coord _ v + b5_lattice Λ F l := by
    change b2_coord _ w = b2_coord _ v + b2_coord _ (b2_latticeMap Λ F l)
    rw [hl, map_sub]
    abel
  change b5_thetaCover Λ F hF Q hQ (b2_coord _ w) = _
  rw [hcoord]
  exact (b54_thetaCover_translate Λ F hF Q hQ l (b2_coord _ v)).symm

theorem b54_theta_continuous (Λ : Type) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    (hF : b2_IsWeightOne Λ F) (Q : LinearMap.BilinForm ℤ Λ)
    (hQ : b2_IsRiemannForm Λ F Q) : Continuous (b5_theta Λ F hF Q hQ) := by
  apply (QuotientAddGroup.isQuotientMap_mk (b2_latticeMap Λ F).range).continuous_iff.mpr
  apply ((b54_thetaCover_continuous Λ F hF Q hQ).comp
    (b2_coordHomeomorph Λ F).continuous).congr
  intro v
  exact (b5_theta_descent_aux Λ F hF Q hQ v).symm

theorem b54_theta_injective (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    Function.Injective (b5_theta Λ F hF Q hQ) := by
  intro t u h
  obtain ⟨l, hl⟩ := b54_thetaCover_eq_lattice Λ F hF Q hQ
    (b2_coord _ (Quotient.out t)) (b2_coord _ (Quotient.out u)) h
  have he : Quotient.out u = Quotient.out t + b2_latticeMap Λ F l := by
    apply (b2_coord _).injective
    rw [map_add]
    exact hl
  have hq : (QuotientAddGroup.mk (Quotient.out u) : b2_torus Λ F) =
      QuotientAddGroup.mk (Quotient.out t) := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    exact ⟨l, by rw [he]; abel⟩
  simpa only [Quotient.out_eq] using hq.symm

theorem b54_theta_isClosedEmbedding (Λ : Type) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    (hF : b2_IsWeightOne Λ F) (Q : LinearMap.BilinForm ℤ Λ)
    (hQ : b2_IsRiemannForm Λ F Q) :
    Topology.IsClosedEmbedding (b5_theta Λ F hF Q hQ) := by
  letI := b2_torus_compactSpace F hF
  letI := b5_projective_aux Λ F hF Q hQ
  exact (b54_theta_continuous Λ F hF Q hQ).isClosedEmbedding
    (b54_theta_injective Λ F hF Q hQ)

theorem b54_theta_surjective (Λ : Type) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    (hF : b2_IsWeightOne Λ F) (Q : LinearMap.BilinForm ℤ Λ)
    (hQ : b2_IsRiemannForm Λ F Q) : Function.Surjective (b5_theta Λ F hF Q hQ) := by
  letI := b5_sections_finite_aux Λ F hF Q hQ 3
  intro p
  obtain ⟨z, hz⟩ := b54_proj_point_is_thetaEvaluation Λ F hF Q
    (Module.finrank ℂ (b5_sections Λ F hF Q 3))
    (Module.finBasis ℂ (b5_sections Λ F hF Q 3))
    (b5_Lcube_basepointFree_aux Λ F hF Q hQ)
    (b5_S_generated_one_aux Λ F hF Q hQ)
    (b54_gradeZero_scalar_bijective Λ F hF Q hQ).2
    (b5_evaluation_irrelevant_aux Λ F hF Q hQ) p
  refine ⟨b2_torusCover Λ F z, ?_⟩
  rw [b2_torusCover, b5_theta_descent_aux]
  have he : b2_coord _ ((b2_coordHomeomorph Λ F).symm z) = z :=
    (b2_coordHomeomorph Λ F).apply_symm_apply z
  rw [he]
  apply CategoryTheory.Over.OverMorphism.ext
  exact hz.symm

theorem b5_theta_homeomorph_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    IsHomeomorph (b5_theta Λ F hF Q hQ) := by
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(b54_theta_isClosedEmbedding Λ F hF Q hQ).isEmbedding,
      b54_theta_surjective Λ F hF Q hQ⟩

open scoped Manifold ContDiff MonoidalCategory

/-- The evaluation homeomorphism, with its inverse determined by bijectivity.
Source: Birkenhake–Lange, Theorem 4.5.1. -/
def b5_thetaEquiv (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    b2_torus Λ F ≃ₜ ComplexPoint (b5_model Λ F hF Q) :=
  (b5_theta_homeomorph_aux Λ F hF Q hQ).homeomorph _

theorem b5_theta_holomorphicFunctions_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b2_latticeMap_discrete F hF
    ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, Fin (TopologicalSpace.dim (b5_model Λ F hF Q).left) → ℂ)
        ω (b5_theta Λ F hF Q hQ) ∧
    ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim (b5_model Λ F hF Q).left) → ℂ) 𝓘(ℂ, b5_V Λ F)
        ω (b5_thetaEquiv Λ F hF Q hQ).symm ∧
    ∀ (U : TopologicalSpace.Opens (ComplexPoint (b5_model Λ F hF Q))) (f : U → ℂ),
      (f4_analytification (b5_model Λ F hF Q)).IsHolFun f ↔
        ∃ g : b5_V Λ F → ℂ,
          DifferentiableOn ℂ g ((b5_thetaCover Λ F hF Q hQ) ⁻¹' (U : Set (ComplexPoint (b5_model Λ F hF Q)))) ∧
          (∀ l z, b5_thetaCover Λ F hF Q hQ z ∈ U →
            g (z + b5_lattice Λ F l) = g z) ∧
          ∀ z : (b5_thetaCover Λ F hF Q hQ) ⁻¹' (U : Set (ComplexPoint (b5_model Λ F hF Q))),
            g z = f ⟨b5_thetaCover Λ F hF Q hQ z, z.property⟩ := by
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b2_latticeMap_discrete F hF
  exact b56_holomorphicFunctions (b5_evaluation_irrelevant_aux Λ F hF Q hQ)
    (b5_thetaCover Λ F hF Q hQ) (fun z ↦ rfl)
    (b56_bpf_of (b5_Lcube_basepointFree_aux Λ F hF Q hQ))
    (b56_tan_of (b5_Lcube_separatesTangents_aux Λ F hF Q hQ)) (b5_theta Λ F hF Q hQ)
    (b5_theta_homeomorph_aux Λ F hF Q hQ)
    (b56_cover_of _ _ (b5_theta_descent_aux Λ F hF Q hQ))

open CategoryTheory.CartesianMonoidalCategory

/-- Addition transported through theta.
Source: Serre, GAGA, §3, Proposition 13; Birkenhake–Lange, §1.1. -/
def b5_addAnalytic (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    ComplexPoint ((b5_model Λ F hF Q) ⊗ (b5_model Λ F hF Q)) → ComplexPoint (b5_model Λ F hF Q) :=
  fun p ↦ b5_theta Λ F hF Q hQ
    ((b5_thetaEquiv Λ F hF Q hQ).symm (Point.map (fst (b5_model Λ F hF Q) (b5_model Λ F hF Q)) p) +
     (b5_thetaEquiv Λ F hF Q hQ).symm (Point.map (snd (b5_model Λ F hF Q) (b5_model Λ F hF Q)) p))

/-- Inversion transported through theta.
Source: Serre, GAGA, §3, Proposition 13; Birkenhake–Lange, §1.1. -/
def b5_negAnalytic (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    ComplexPoint (b5_model Λ F hF Q) → ComplexPoint (b5_model Λ F hF Q) :=
  fun p ↦ b5_theta Λ F hF Q hQ (-(b5_thetaEquiv Λ F hF Q hQ).symm p)

theorem b5_add_graph_isIso_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    IsIso (b5_graphFirst ((b5_model Λ F hF Q) ⊗ (b5_model Λ F hF Q)) (b5_model Λ F hF Q) (b5_addAnalytic Λ F hF Q hQ)) := by
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b2_latticeMap_discrete F hF
  obtain ⟨hθ, hθs, -⟩ := b5_theta_holomorphicFunctions_aux Λ F hF Q hQ
  obtain ⟨C, hC, hg⟩ := b55_add_closed _ (b5_thetaEquiv Λ F hF Q hQ) hθ hθs
  have : IsIntegral ((b5_model Λ F hF Q) ⊗ (b5_model Λ F hF Q)).left :=
    HodgeLean.Adapters.gagam_product_isIntegral _ _
  have : Smooth ((b5_model Λ F hF Q) ⊗ (b5_model Λ F hF Q)).hom :=
    HodgeLean.Adapters.gagam_product_smooth _ _
  have : IsProjective ((b5_model Λ F hF Q) ⊗ (b5_model Λ F hF Q)).hom :=
    HodgeLean.Adapters.gagam_product_projective _ _
  exact b55_graphFirst_isIso _ _ _ C hC hg

/-- Algebraic add from the inverse first graph projection.
Source: Serre, GAGA, §3, Proposition 13; Birkenhake–Lange, §1.1. -/
def b5_add (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    ((b5_model Λ F hF Q) ⊗ (b5_model Λ F hF Q)) ⟶ (b5_model Λ F hF Q) :=
  letI := b5_add_graph_isIso_aux Λ F hF Q hQ
  inv (b5_graphFirst ((b5_model Λ F hF Q) ⊗ (b5_model Λ F hF Q)) (b5_model Λ F hF Q) (b5_addAnalytic Λ F hF Q hQ)) ≫
    b5_graphSecond ((b5_model Λ F hF Q) ⊗ (b5_model Λ F hF Q)) (b5_model Λ F hF Q) (b5_addAnalytic Λ F hF Q hQ)

theorem b5_neg_graph_isIso_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    IsIso (b5_graphFirst (b5_model Λ F hF Q) (b5_model Λ F hF Q) (b5_negAnalytic Λ F hF Q hQ)) := by
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b2_latticeMap_discrete F hF
  obtain ⟨hθ, hθs, -⟩ := b5_theta_holomorphicFunctions_aux Λ F hF Q hQ
  obtain ⟨C, hC, hg⟩ := b55_neg_closed _ (b5_thetaEquiv Λ F hF Q hQ) hθ hθs
  exact b55_graphFirst_isIso _ _ _ C hC hg

/-- Algebraic neg from the inverse first graph projection.
Source: Serre, GAGA, §3, Proposition 13; Birkenhake–Lange, §1.1. -/
def b5_neg (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    (b5_model Λ F hF Q) ⟶ (b5_model Λ F hF Q) :=
  letI := b5_neg_graph_isIso_aux Λ F hF Q hQ
  inv (b5_graphFirst (b5_model Λ F hF Q) (b5_model Λ F hF Q) (b5_negAnalytic Λ F hF Q hQ)) ≫
    b5_graphSecond (b5_model Λ F hF Q) (b5_model Λ F hF Q) (b5_negAnalytic Λ F hF Q hQ)

/-- The identity morphism is evaluation at the zero torus class.
Source: Serre, GAGA, §3, Proposition 13; Birkenhake–Lange, §1.1. -/
def b5_identity (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    𝟙_ (Over (Spec ↧ℂ)) ⟶ (b5_model Λ F hF Q) :=
  b5_theta Λ F hF Q hQ 0

theorem b5_group_laws_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    (b5_identity Λ F hF Q hQ ▷ (b5_model Λ F hF Q)) ≫ b5_add Λ F hF Q hQ = (λ_ (b5_model Λ F hF Q)).hom ∧
    ((b5_model Λ F hF Q) ◁ b5_identity Λ F hF Q hQ) ≫ b5_add Λ F hF Q hQ = (ρ_ (b5_model Λ F hF Q)).hom ∧
    (b5_add Λ F hF Q hQ ▷ (b5_model Λ F hF Q)) ≫ b5_add Λ F hF Q hQ =
      (α_ (b5_model Λ F hF Q) (b5_model Λ F hF Q) (b5_model Λ F hF Q)).hom ≫ ((b5_model Λ F hF Q) ◁ b5_add Λ F hF Q hQ) ≫ b5_add Λ F hF Q hQ ∧
    lift (b5_neg Λ F hF Q hQ) (𝟙 (b5_model Λ F hF Q)) ≫ b5_add Λ F hF Q hQ = toUnit (b5_model Λ F hF Q) ≫ b5_identity Λ F hF Q hQ ∧
    lift (𝟙 (b5_model Λ F hF Q)) (b5_neg Λ F hF Q hQ) ≫ b5_add Λ F hF Q hQ = toUnit (b5_model Λ F hF Q) ≫ b5_identity Λ F hF Q hQ ∧
    (β_ (b5_model Λ F hF Q) (b5_model Λ F hF Q)).hom ≫ b5_add Λ F hF Q hQ = b5_add Λ F hF Q hQ := by
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b2_latticeMap_discrete F hF
  obtain ⟨hθ, hθs, -⟩ := b5_theta_holomorphicFunctions_aux Λ F hF Q hQ
  obtain ⟨Ca, hCa, hga⟩ := b55_add_closed _ (b5_thetaEquiv Λ F hF Q hQ) hθ hθs
  obtain ⟨Cn, hCn, hgn⟩ := b55_neg_closed _ (b5_thetaEquiv Λ F hF Q hQ) hθ hθs
  have := b5_add_graph_isIso_aux Λ F hF Q hQ
  have := b5_neg_graph_isIso_aux Λ F hF Q hQ
  have hadd : Point.map (b5_add Λ F hF Q hQ) = b5_addAnalytic Λ F hF Q hQ :=
    b55_pointMap_graph _ _ (b5_addAnalytic Λ F hF Q hQ) Ca hCa hga
  have hneg : Point.map (b5_neg Λ F hF Q hQ) = b5_negAnalytic Λ F hF Q hQ :=
    b55_pointMap_graph _ _ (b5_negAnalytic Λ F hF Q hQ) Cn hCn hgn
  exact b55_group_laws _ (b5_thetaEquiv Λ F hF Q hQ).toEquiv _ _ hadd hneg

/-- The group object with the named algebraic operations.
Source: Serre, GAGA, §3, Proposition 13; Birkenhake–Lange, §1.1. -/
def b5_groupObj (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    GrpObj (b5_model Λ F hF Q) :=
  { one := b5_identity Λ F hF Q hQ
    mul := b5_add Λ F hF Q hQ
    inv := b5_neg Λ F hF Q hQ
    one_mul := (b5_group_laws_aux Λ F hF Q hQ).1
    mul_one := (b5_group_laws_aux Λ F hF Q hQ).2.1
    mul_assoc := (b5_group_laws_aux Λ F hF Q hQ).2.2.1
    left_inv := (b5_group_laws_aux Λ F hF Q hQ).2.2.2.1
    right_inv := (b5_group_laws_aux Λ F hF Q hQ).2.2.2.2.1 }

theorem b5_commutative_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    IsCommMonObj (b5_model Λ F hF Q) := by
  letI := b5_groupObj Λ F hF Q hQ
  exact ⟨(b5_group_laws_aux Λ F hF Q hQ).2.2.2.2.2⟩

theorem b5_group_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    b5_theta Λ F hF Q hQ 0 = 1 ∧
    (∀ t u, b5_theta Λ F hF Q hQ (t + u) = b5_theta Λ F hF Q hQ t * b5_theta Λ F hF Q hQ u) ∧
    (∀ t, b5_theta Λ F hF Q hQ (-t) = (b5_theta Λ F hF Q hQ t)⁻¹) := by
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b2_latticeMap_discrete F hF
  obtain ⟨hθ, hθs, -⟩ := b5_theta_holomorphicFunctions_aux Λ F hF Q hQ
  obtain ⟨Ca, hCa, hga⟩ := b55_add_closed _ (b5_thetaEquiv Λ F hF Q hQ) hθ hθs
  obtain ⟨Cn, hCn, hgn⟩ := b55_neg_closed _ (b5_thetaEquiv Λ F hF Q hQ) hθ hθs
  have := b5_add_graph_isIso_aux Λ F hF Q hQ
  have := b5_neg_graph_isIso_aux Λ F hF Q hQ
  have hadd : Point.map (b5_add Λ F hF Q hQ) = b5_addAnalytic Λ F hF Q hQ :=
    b55_pointMap_graph _ _ (b5_addAnalytic Λ F hF Q hQ) Ca hCa hga
  have hneg : Point.map (b5_neg Λ F hF Q hQ) = b5_negAnalytic Λ F hF Q hQ :=
    b55_pointMap_graph _ _ (b5_negAnalytic Λ F hF Q hQ) Cn hCn hgn
  letI := b5_groupObj Λ F hF Q hQ
  exact b55_group_points _ (b5_thetaEquiv Λ F hF Q hQ).toEquiv _ _ hadd hneg rfl rfl rfl

/-- The differential of the theta map in the exponential identity coordinates.
Source: Birkenhake–Lange, §1.1 and §2.2. -/
def b5_periodDerivative (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b5_V Λ F →ₗ[ℂ] (Fin (TopologicalSpace.dim (b5_model Λ F hF Q).left) → ℂ) :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  (fderiv ℂ (fun z ↦ identityChart (b5_model Λ F hF Q) (TopologicalSpace.dim (b5_model Λ F hF Q).left)
    (b5_thetaCover Λ F hF Q hQ z)) 0).toLinearMap

theorem b5_periodDerivative_bijective_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    Function.Bijective (b5_periodDerivative Λ F hF Q hQ) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI := b2_latticeMap_discrete F hF
  have hθP := b56_cover_of _ _ (b5_theta_descent_aux Λ F hF Q hQ)
  have hP0 : b5_thetaCover Λ F hF Q hQ 0 = 1 := by
    rw [← hθP, ← (b5_group_aux Λ F hF Q hQ).1]
    congr 1
    simp [b2_torusCover, b2_coordHomeomorph]
  exact b56_identityChart_fderiv_bijective (b5_evaluation_irrelevant_aux Λ F hF Q hQ)
    (b5_thetaCover Λ F hF Q hQ) (fun z ↦ rfl) (b56_bpf_of (b5_Lcube_basepointFree_aux Λ F hF Q hQ))
    (b5_theta Λ F hF Q hQ) hθP _ (b56_tan_of (b5_Lcube_separatesTangents_aux Λ F hF Q hQ))
    (b5_theta_homeomorph_aux Λ F hF Q hQ) hP0

/-- The linear period identification induced by the theta differential.
Source: Birkenhake–Lange, §1.1 and §2.2. -/
def b5_periodLinearEquiv (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b5_V Λ F ≃ₗ[ℂ] (Fin (TopologicalSpace.dim (b5_model Λ F hF Q).left) → ℂ) :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  LinearEquiv.ofBijective (b5_periodDerivative Λ F hF Q hQ) (b5_periodDerivative_bijective_aux Λ F hF Q hQ)

theorem b5_periodDerivative_lattice_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l : Λ, b5_periodDerivative Λ F hF Q hQ (b5_lattice Λ F l) ∈
      HodgeLean.Adapters.abelianPeriodLattice (b5_model Λ F hF Q) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI := b2_latticeMap_discrete F hF
  have hθP := b56_cover_of _ _ (b5_theta_descent_aux Λ F hF Q hQ)
  haveI : IsCommMonObj (b5_model Λ F hF Q) := b5_commutative_aux Λ F hF Q hQ
  intro l
  exact b56_exp_lattice (b5_evaluation_irrelevant_aux Λ F hF Q hQ)
    (b5_thetaCover Λ F hF Q hQ) (fun z ↦ rfl) (b56_bpf_of (b5_Lcube_basepointFree_aux Λ F hF Q hQ))
    (b5_theta Λ F hF Q hQ) hθP _ (b5_group_aux Λ F hF Q hQ).1 (b5_group_aux Λ F hF Q hQ).2.1 l

/-- The integral map induced by the differential on lattice vectors.
Source: Birkenhake–Lange, §1.1 and §2.2. -/
def b5_periodMap (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    Λ →+ b2_abelianLattice (b5_model Λ F hF Q) :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  ((b5_periodDerivative Λ F hF Q hQ).restrictScalars ℤ |>.comp (b5_lattice Λ F)).codRestrict
    (HodgeLean.Adapters.abelianPeriodLattice (b5_model Λ F hF Q))
    (b5_periodDerivative_lattice_aux Λ F hF Q hQ) |>.toAddMonoidHom

theorem b5_periodMap_bijective_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    Function.Bijective (b5_periodMap Λ F hF Q hQ) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  letI := b2_latticeMap_discrete F hF
  have hθP := b56_cover_of _ _ (b5_theta_descent_aux Λ F hF Q hQ)
  haveI : IsCommMonObj (b5_model Λ F hF Q) := b5_commutative_aux Λ F hF Q hQ
  have hD := b5_periodDerivative_bijective_aux Λ F hF Q hQ
  refine ⟨fun l m h ↦ ?_, fun w ↦ ?_⟩
  · exact b52_lattice_injective Λ F hF (hD.1 (congrArg Subtype.val h))
  · obtain ⟨l, hl⟩ := b56_period_surjective (b5_evaluation_irrelevant_aux Λ F hF Q hQ)
      (b5_thetaCover Λ F hF Q hQ) (fun z ↦ rfl)
      (b56_bpf_of (b5_Lcube_basepointFree_aux Λ F hF Q hQ)) (b5_theta Λ F hF Q hQ) hθP _
      (b5_theta_homeomorph_aux Λ F hF Q hQ).injective (b5_group_aux Λ F hF Q hQ).1
      (b5_group_aux Λ F hF Q hQ).2.1 hD.2 w.1 w.2
    exact ⟨l, Subtype.ext hl⟩

/-- The integral lattice equivalence for the B4b interface.
Source: Birkenhake–Lange, §1.1 and §2.2. -/
def b5_periodEquiv (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    Λ ≃+ b2_abelianLattice (b5_model Λ F hF Q) :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  AddEquiv.ofBijective (b5_periodMap Λ F hF Q hQ) (b5_periodMap_bijective_aux Λ F hF Q hQ)

theorem b5_period_filtration_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    F.map (b2_cplxMap (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom) = b2_abelianF (b5_model Λ F hF Q) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  exact b56_filtration_eq (HodgeLean.Adapters.abelianPeriodLattice (b5_model Λ F hF Q))
    (b5_periodEquiv Λ F hF Q hQ).toAddMonoidHom (b5_periodEquiv Λ F hF Q hQ).surjective
    (b5_periodDerivative Λ F hF Q hQ) (b5_periodDerivative_bijective_aux Λ F hF Q hQ).1
    (fun l ↦ rfl)

/-- The original Appell–Humbert Chern pairing in period coordinates, before the third power.
Source: Birkenhake–Lange, §1.1 and §2.2. -/
def b5_originalChernPairing (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    b2_abelianLattice (b5_model Λ F hF Q) → b2_abelianLattice (b5_model Λ F hF Q) → ℤ :=
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  fun l m ↦ ⌊(b5_H Λ F hF Q
    ((b5_periodLinearEquiv Λ F hF Q hQ).symm l.val)
    ((b5_periodLinearEquiv Λ F hF Q hQ).symm m.val)).im⌋

theorem b5_polarization_normalized_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l m : Λ,
      b5_originalChernPairing Λ F hF Q hQ (b5_periodEquiv Λ F hF Q hQ l) (b5_periodEquiv Λ F hF Q hQ m) = Q l m := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  intro l m
  have hsymm (k : Λ) : (b5_periodLinearEquiv Λ F hF Q hQ).symm
      (b5_periodEquiv Λ F hF Q hQ k).val = b5_lattice Λ F k :=
    (b5_periodLinearEquiv Λ F hF Q hQ).symm_apply_apply (b5_lattice Λ F k)
  change ⌊(b5_H Λ F hF Q _ _).im⌋ = Q l m
  rw [hsymm, hsymm, b5_imaginary_lattice_aux Λ F hF Q hQ l m, Int.floor_intCast]

theorem b5_originalChernPairing_integral_aux (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    ∀ l m : b2_abelianLattice (b5_model Λ F hF Q),
      (b5_H Λ F hF Q ((b5_periodLinearEquiv Λ F hF Q hQ).symm l.val)
        ((b5_periodLinearEquiv Λ F hF Q hQ).symm m.val)).im =
      (b5_originalChernPairing Λ F hF Q hQ l m : ℝ) := by
  letI := b5_groupObj Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  letI := b5_smooth_aux Λ F hF Q hQ
  letI := b5_projective_aux Λ F hF Q hQ
  intro l m
  obtain ⟨k, rfl⟩ := (b5_periodMap_bijective_aux Λ F hF Q hQ).2 l
  obtain ⟨k', rfl⟩ := (b5_periodMap_bijective_aux Λ F hF Q hQ).2 m
  have hsymm (j : Λ) : (b5_periodLinearEquiv Λ F hF Q hQ).symm
      (b5_periodMap Λ F hF Q hQ j).val = b5_lattice Λ F j :=
    (b5_periodLinearEquiv Λ F hF Q hQ).symm_apply_apply (b5_lattice Λ F j)
  change (b5_H Λ F hF Q _ _).im = ((⌊(b5_H Λ F hF Q _ _).im⌋ : ℤ) : ℝ)
  rw [hsymm, hsymm, b5_imaginary_lattice_aux Λ F hF Q hQ k k', Int.floor_intCast]

end HodgeLean.Foundations.Program
