import HodgeLean.RealDefs.WeilClasses
import HodgeLean.Blocks.Weil.RationalKernel
import HodgeLean.Foundations.HodgeLieAlgebra
import HodgeLean.Foundations.CMSplitting
import HodgeLean.Blocks.HodgeStructure.DirectSum

/-! # Cyclotomic determinant carriers

The field action is supplied by free coordinates, never by a selected class space.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry ComplexPoint
open HodgeLean.RealDefs

namespace HodgeLean.Foundations

/-- The cyclotomic coefficient field.
Source: G32 v0.16, Section 4.1, Schoen suppliers. -/
abbrev cyc_Field (m : ℕ) := CyclotomicField m ℚ

example : Field (cyc_Field 3) := inferInstance

/-- Scalar multiplication transported through free field coordinates.
Source: G32 v0.16, Section 4.1, the action on primitive cohomology. -/
def cyc_scalar {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (a : cyc_Field m) : Module.End ℚ V :=
  e.symm.toLinearMap ∘ₗ
    (LinearMap.pi fun i => (LinearMap.mulLeft ℚ a) ∘ₗ LinearMap.proj i) ∘ₗ e.toLinearMap

example {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (a : cyc_Field m) (v : V) :
    cyc_scalar e a v = e.symm (fun i => a * e v i) := rfl

/-- The simultaneous eigenspace belonging to a field embedding.
Source: G32 v0.16, Section 4.1, the spaces `V_t`. -/
def cyc_eigenspace {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    Submodule ℂ (ℂ ⊗[ℚ] V) :=
  ⨅ a : cyc_Field m, Module.End.eigenspace ((cyc_scalar e a).baseChange ℂ) (t a)

example {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    cyc_eigenspace e t ≤ Module.End.eigenspace
      ((cyc_scalar e 1).baseChange ℂ) (t 1) := iInf_le _ 1

/-- A positive even free-rank cyclotomic action with balanced signature.
Free coordinates specify the field action itself. Preservation of Hodge pieces and
signature dimensions concern degree one only.
Source: G32 v0.16, Section 4.1; Schoen (1988), Section 1. -/
structure cyc_Action {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (M : HodgeBlocks.QHodgeStructure 1 V) (m k : ℕ) where
  cyc_order : 3 ≤ m
  cyc_positive : 0 < k
  cyc_coordinates : V ≃ₗ[ℚ] (Fin (2 * k) → cyc_Field m)
  cyc_preserves : ∀ a pq, (M.H pq).map
    ((cyc_scalar cyc_coordinates a).baseChange ℂ) ≤ M.H pq
  cyc_signature : ∀ t : cyc_Field m →ₐ[ℚ] ℂ,
    Module.finrank ℂ ↥(cyc_eigenspace cyc_coordinates t ⊓ M.H (1, 0)) = k

example {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {M : HodgeBlocks.QHodgeStructure 1 V} {m k : ℕ} (A : cyc_Action M m k) :
    0 < 2 * k := Nat.mul_pos (by norm_num) A.cyc_positive

/-- The determinant line for one primitive embedding, inside the rational-degree exterior
power after extension of scalars.
Source: G32 v0.16, Section 4.1, `det V_t`. -/
def cyc_line {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    Submodule ℂ (⋀[ℂ]^h (ℂ ⊗[ℚ] V)) :=
  LinearMap.range (exteriorPower.map h (cyc_eigenspace e t).subtype)

example {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    cyc_line e t = LinearMap.range
      (exteriorPower.map h (cyc_eigenspace e t).subtype) := rfl

/-- The sum of all primitive determinant lines.
Source: G32 v0.16, Section 4.1, the displayed scalar-extension identity. -/
def cyc_topLines {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    Submodule ℂ (⋀[ℂ]^h (ℂ ⊗[ℚ] V)) := ⨆ t, cyc_line e t

example {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    cyc_line e t ≤ cyc_topLines e := le_iSup (cyc_line e) t

/-- Rational descent of the primitive determinant sum, as an actual submodule of wedges.
Source: G32 v0.16, Section 4.1; the quadratic model `WeilAction.weilClasses`. -/
def cyc_wedges {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) : Submodule ℚ (⋀[ℚ]^h V) :=
  (cyc_topLines e).restrictScalars ℚ |>.comap (HodgeBlocks.complexifyWedge h)

example {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (w : ⋀[ℚ]^h V) :
    w ∈ cyc_wedges e ↔ HodgeBlocks.complexifyWedge h w ∈ cyc_topLines e := Iff.rfl

/-- The determinant classes carried to geometric cohomology by the cup map.
Source: G32 v0.16, Section 4.1, `W_F(P)`; `RealDefs.weilClassOf`. -/
def cyc_classSpace {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) {m h : ℕ}
    (e : HQ X 1 ≃ₗ[ℚ] (Fin h → cyc_Field m)) : Submodule ℚ (HQ X h) :=
  (cyc_wedges e).map (μ.cupWedgeMap h)

example {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) {m h : ℕ}
    (e : HQ X 1 ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    cyc_classSpace μ e = (cyc_wedges e).map (μ.cupWedgeMap h) := rfl

/-- Algebraicity of every cyclotomic determinant class in positive even degree.
Source: G32 v0.16, Lemma 4.2; Schoen (1988), Corollary 3.1. -/
def cyc_Algebraic {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) {m k : ℕ}
    (e : HQ X 1 ≃ₗ[ℚ] (Fin (2 * k) → cyc_Field m)) : Prop :=
  cyc_classSpace μ e ≤ algebraicCycleClassSpan X k

example {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) {m k : ℕ}
    (e : HQ X 1 ≃ₗ[ℚ] (Fin (2 * k) → cyc_Field m)) :
    cyc_Algebraic μ e ↔ cyc_classSpace μ e ≤ algebraicCycleClassSpan X k := Iff.rfl

/-- The regular action as an algebra homomorphism, with no selected eigenspaces.
Source: G32 v0.16, Section 4.1, the free field action. -/
def cyc_rep {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) : cyc_Field m →ₐ[ℚ] Module.End ℚ V where
  toFun := cyc_scalar e
  map_zero' := by
    ext v
    change e.symm (fun i => 0 * e v i) = 0
    simp only [zero_mul]
    change e.symm 0 = 0
    exact map_zero _
  map_one' := by
    ext v
    change e.symm (fun i => 1 * e v i) = v
    simp only [one_mul, e.symm_apply_apply]
  map_add' a b := by
    ext v
    change e.symm (fun i => (a + b) * e v i) =
      e.symm (fun i => a * e v i) + e.symm (fun i => b * e v i)
    rw [← map_add]
    congr 1
    funext i
    exact add_mul a b (e v i)
  map_mul' a b := by
    ext v
    change e.symm (fun i => (a * b) * e v i) =
      e.symm (fun i => a * e (e.symm (fun j => b * e v j)) i)
    rw [e.apply_symm_apply]
    congr 1
    funext i
    exact mul_assoc a b (e v i)
  commutes' r := by
    ext v
    apply e.injective
    change e (e.symm (fun i => algebraMap ℚ _ r * e v i)) = e (r • v)
    rw [e.apply_symm_apply, map_smul]
    ext i
    exact (Algebra.smul_def r (e v i)).symm

example {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (a : cyc_Field m) :
    cyc_rep e a = cyc_scalar e a := rfl

/-- Cyclotomic extension evidence for the chosen coefficient field.
Source: Mathlib, CyclotomicField.isCyclotomicExtension. -/
instance cyc_fieldCyclotomic (m : ℕ) [NeZero m] :
    IsCyclotomicExtension {m} ℚ (cyc_Field m) :=
  CyclotomicField.isCyclotomicExtension m ℚ

example : IsCyclotomicExtension {4} ℚ (cyc_Field 4) := inferInstance

/-- A primitive fourth root in the test field.
Source: the cyclotomic construction, G32 v0.16, Section 4.1. -/
def cyc_i : cyc_Field 4 := IsCyclotomicExtension.zeta 4 ℚ (cyc_Field 4)

example : IsPrimitiveRoot cyc_i 4 := IsCyclotomicExtension.zeta_spec 4 ℚ (cyc_Field 4)

theorem cyc_i_sq : cyc_i ^ 2 = -1 := by
  have h := IsCyclotomicExtension.zeta_spec 4 ℚ (cyc_Field 4)
  have hsq : (cyc_i ^ 2) ^ 2 = 1 := by simpa [cyc_i, ← pow_mul] using h.pow_eq_one
  exact (sq_eq_one_iff.mp hsq).resolve_left
    (h.pow_ne_one_of_pos_of_lt (l := 2) (by norm_num) (by norm_num))

/-- Multiplication by the primitive fourth root on the regular field module.
Source: Silverman, Advanced Topics, Chapter II, the rational CM action. -/
def cyc_rotation : Module.End ℚ (cyc_Field 4) := LinearMap.mulLeft ℚ cyc_i

example (x : cyc_Field 4) : cyc_rotation x = cyc_i * x := rfl

theorem cyc_rotation_sq : cyc_rotation * cyc_rotation = -1 := by
  ext x
  change cyc_i * (cyc_i * x) = -x
  rw [← mul_assoc, ← pow_two, cyc_i_sq, neg_one_mul]

/-- The two CM weight-one structures on the regular quadratic field.
The Boolean exchanges the CM type; their product has balanced signature.
Source: Silverman, Advanced Topics, Chapter II; Birkenhake–Lange, Chapter 1. -/
def cyc_ellipticHodge (swap : Bool) : HodgeBlocks.QHodgeStructure 1 (cyc_Field 4) where
  H := complexStructureHodge cyc_rotation (if swap then 0 else 1) (if swap then 1 else 0)
  supported pq hpq := by
    apply complexStructureHodge_pure
    cases swap <;> simpa using hpq
  isInternal := isInternal_complexStructureHodge cyc_rotation_sq (by cases swap <;> norm_num)
  conj_symm p q := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact complexStructureHodge_conj (by cases swap <;> norm_num) p q x hx
    · intro x hx
      refine ⟨HodgeBlocks.sigmaQ _ x,
        complexStructureHodge_conj (by cases swap <;> norm_num) q p x hx, ?_⟩
      exact HodgeBlocks.sigmaQ_involutive _ x

example : (cyc_ellipticHodge false).H (1, 0) =
    Module.End.eigenspace (cyc_rotation.baseChange ℂ) (-Complex.I) := rfl

/-- The rational Hodge model of the product of the two opposite CM elliptic types.
Source: Silverman, Advanced Topics, Chapter II; Birkenhake–Lange, Chapter 1. -/
def cyc_productHodge : HodgeBlocks.QHodgeStructure 1 (cyc_Field 4 × cyc_Field 4) :=
  HodgeBlocks.QHodgeStructure.prod (cyc_Field 4) (cyc_Field 4)
    (cyc_ellipticHodge false) (cyc_ellipticHodge true)

example : Module.finrank ℚ (cyc_Field 4 × cyc_Field 4) = 4 := by
  have h : Module.finrank ℚ (cyc_Field 4) = 2 := by
    exact (IsCyclotomicExtension.finrank (cyc_Field 4)
      (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 4))).trans (by decide)
  rw [Module.finrank_prod, h]

/-- Free rank-two coordinates for the product test.
Source: the direct product of the two regular field modules. -/
def cyc_productCoordinates : (cyc_Field 4 × cyc_Field 4) ≃ₗ[ℚ]
    (Fin (2 * 1) → cyc_Field 4) := (LinearEquiv.finTwoArrow ℚ (cyc_Field 4)).symm

example (x : cyc_Field 4 × cyc_Field 4) :
    cyc_productCoordinates x = ![x.1, x.2] := rfl

theorem cyc_commuting_preserves {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T U : Module.End ℂ V) (h : T.comp U = U.comp T) (s : ℂ) :
    (Module.End.eigenspace T s).map U ≤ Module.End.eigenspace T s := by
  rintro _ ⟨x, hx, rfl⟩
  change x ∈ Module.End.eigenspace T s at hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  calc
    T (U x) = U (T x) := LinearMap.congr_fun h x
    _ = s • U x := by rw [hx, map_smul]

theorem cyc_regular_preserves (a : cyc_Field 4) (swap : Bool) (pq : ℤ × ℤ) :
    ((cyc_ellipticHodge swap).H pq).map ((LinearMap.mulLeft ℚ a).baseChange ℂ) ≤
      (cyc_ellipticHodge swap).H pq := by
  have hc : cyc_rotation.comp (LinearMap.mulLeft ℚ a) =
      (LinearMap.mulLeft ℚ a).comp cyc_rotation := by
    ext x
    change cyc_i * (a * x) = a * (cyc_i * x)
    ring
  have hcc := congrArg (LinearMap.baseChange ℂ) hc
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hcc
  change (complexStructureHodge cyc_rotation _ _ pq).map _ ≤
    complexStructureHodge cyc_rotation _ _ pq
  cases swap <;> unfold complexStructureHodge <;> split_ifs <;>
    first | exact cyc_commuting_preserves _ _ hcc _ | rw [Submodule.map_bot]

/-- A quadratic action used only to verify the test model's eigenspace dimensions.
Source: the regular Q(i) action on the CM elliptic Hodge structure. -/
def cyc_regularWeil : HodgeBlocks.WeilAction (cyc_ellipticHodge false) 1 where
  J := cyc_rotation
  J_sq := by simpa only [Module.End.mul_eq_comp, neg_smul, one_smul,
    Module.End.one_eq_id] using cyc_rotation_sq
  preserves := cyc_regular_preserves cyc_i false

example : cyc_regularWeil.J = cyc_rotation := rfl

theorem cyc_regular_eigen_ranks :
    Module.finrank ℂ ↥(Module.End.eigenspace (cyc_rotation.baseChange ℂ) Complex.I) = 1 ∧
    Module.finrank ℂ ↥(Module.End.eigenspace (cyc_rotation.baseChange ℂ) (-Complex.I)) = 1 := by
  have hc := isCompl_eigenspace_of_sq cyc_rotation_sq
  have hd := Submodule.finrank_add_eq_of_isCompl hc
  have hF : Module.finrank ℚ (cyc_Field 4) = 2 := by
    exact (IsCyclotomicExtension.finrank (cyc_Field 4)
      (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 4))).trans (by decide)
  rw [Module.finrank_baseChange, hF] at hd
  have heq := cyc_regularWeil.finrank_Vsbar_eq_Vs
  have hω : HodgeBlocks.WeilAction.omegaC 1 = Complex.I := by
    norm_num [HodgeBlocks.WeilAction.omegaC]
  change Module.finrank ℂ ↥(Module.End.eigenspace (cyc_rotation.baseChange ℂ)
    (-HodgeBlocks.WeilAction.omegaC 1)) =
    Module.finrank ℂ ↥(Module.End.eigenspace (cyc_rotation.baseChange ℂ)
      (HodgeBlocks.WeilAction.omegaC 1)) at heq
  rw [hω] at heq
  omega

theorem cyc_generator_eigen_iff {V : Type*} [AddCommGroup V] [Module ℚ V] {h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field 4)) (t : cyc_Field 4 →ₐ[ℚ] ℂ)
    (x : ℂ ⊗[ℚ] V) :
    x ∈ cyc_eigenspace e t ↔ (cyc_scalar e cyc_i).baseChange ℂ x = t cyc_i • x := by
  constructor
  · intro hx
    simp only [cyc_eigenspace, Submodule.mem_iInf] at hx
    exact Module.End.mem_eigenspace_iff.mp (hx cyc_i)
  · intro hx
    have ht : Algebra.adjoin ℚ ({cyc_i} : Set (cyc_Field 4)) = ⊤ := by
      exact IsCyclotomicExtension.adjoin_primitive_root_eq_top
        (IsCyclotomicExtension.zeta_spec 4 ℚ (cyc_Field 4))
    exact a2a_eigenspace_gen_le (cyc_rep e) ht t
      (Module.End.mem_eigenspace_iff.mpr hx)

theorem cyc_product_scalar_baseChange (a : cyc_Field 4)
    (x : ℂ ⊗[ℚ] (cyc_Field 4 × cyc_Field 4)) :
    HodgeBlocks.prodBaseChange _ _ ((cyc_scalar cyc_productCoordinates a).baseChange ℂ x) =
      (((LinearMap.mulLeft ℚ a).baseChange ℂ) (HodgeBlocks.prodBaseChange _ _ x).1,
       ((LinearMap.mulLeft ℚ a).baseChange ℂ) (HodgeBlocks.prodBaseChange _ _ x).2) := by
  induction x using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy =>
      simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

theorem cyc_product_preserves (a : cyc_Field 4) (pq : ℤ × ℤ) :
    (cyc_productHodge.H pq).map
      ((cyc_scalar cyc_productCoordinates a).baseChange ℂ) ≤ cyc_productHodge.H pq := by
  rintro _ ⟨x, hx, rfl⟩
  change _ ∈ (Submodule.prod ((cyc_ellipticHodge false).H pq)
    ((cyc_ellipticHodge true).H pq)).map
      (HodgeBlocks.prodBaseChange _ _).symm.toLinearMap at hx ⊢
  rw [Submodule.mem_map_equiv] at hx ⊢
  simp only [LinearEquiv.symm_symm] at hx ⊢
  rw [cyc_product_scalar_baseChange]
  exact ⟨cyc_regular_preserves a false pq (Submodule.mem_map_of_mem hx.1),
    cyc_regular_preserves a true pq (Submodule.mem_map_of_mem hx.2)⟩

theorem cyc_product_eigenspace (t : cyc_Field 4 →ₐ[ℚ] ℂ) :
    cyc_eigenspace cyc_productCoordinates t =
      ((Module.End.eigenspace (cyc_rotation.baseChange ℂ) (t cyc_i)).prod
        (Module.End.eigenspace (cyc_rotation.baseChange ℂ) (t cyc_i))).map
          (HodgeBlocks.prodBaseChange _ _).symm.toLinearMap := by
  ext x
  rw [cyc_generator_eigen_iff, Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_symm]
  constructor
  · intro hx
    have h := congrArg (HodgeBlocks.prodBaseChange (cyc_Field 4) (cyc_Field 4)) hx
    rw [cyc_product_scalar_baseChange, map_smul] at h
    exact ⟨Module.End.mem_eigenspace_iff.mpr (congrArg Prod.fst h),
      Module.End.mem_eigenspace_iff.mpr (congrArg Prod.snd h)⟩
  · intro hx
    apply (HodgeBlocks.prodBaseChange _ _).injective
    rw [cyc_product_scalar_baseChange, map_smul]
    exact Prod.ext (Module.End.mem_eigenspace_iff.mp hx.1)
      (Module.End.mem_eigenspace_iff.mp hx.2)

theorem cyc_product_signature (t : cyc_Field 4 →ₐ[ℚ] ℂ) :
    Module.finrank ℂ ↥(cyc_eigenspace cyc_productCoordinates t ⊓
      cyc_productHodge.H (1, 0)) = 1 := by
  have ht : t cyc_i = Complex.I ∨ t cyc_i = -Complex.I := by
    have hsq : (t cyc_i) ^ 2 = Complex.I ^ 2 := by
      rw [← map_pow, cyc_i_sq, map_neg, map_one, Complex.I_sq]
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp hsq
  have hi : (Module.End.eigenspace (cyc_rotation.baseChange ℂ) Complex.I) ⊓
      (Module.End.eigenspace (cyc_rotation.baseChange ℂ) (-Complex.I)) = ⊥ :=
    (isCompl_eigenspace_of_sq cyc_rotation_sq).disjoint.symm.eq_bot
  rw [cyc_product_eigenspace]
  change Module.finrank ℂ ↥(((Module.End.eigenspace (cyc_rotation.baseChange ℂ) (t cyc_i)).prod
    (Module.End.eigenspace (cyc_rotation.baseChange ℂ) (t cyc_i))).map
    (HodgeBlocks.prodBaseChange _ _).symm.toLinearMap ⊓
    ((Module.End.eigenspace (cyc_rotation.baseChange ℂ) (-Complex.I)).prod
      (Module.End.eigenspace (cyc_rotation.baseChange ℂ) Complex.I)).map
        (HodgeBlocks.prodBaseChange _ _).symm.toLinearMap) = 1
  rw [← Submodule.map_inf _ (HodgeBlocks.prodBaseChange _ _).symm.injective,
    LinearEquiv.finrank_map_eq,
    Submodule.prod_inf_prod]
  rcases ht with ht | ht
  · rw [ht, hi, inf_idem]
    let P := Module.End.eigenspace (cyc_rotation.baseChange ℂ) Complex.I
    let e : ↥((⊥ : Submodule ℂ (ℂ ⊗[ℚ] cyc_Field 4)).prod P) ≃ₗ[ℂ] P :=
      { toFun := fun x => ⟨x.1.2, x.2.2⟩
        invFun := fun x => ⟨(0, x.1), ⟨Submodule.zero_mem _, x.2⟩⟩
        left_inv := by intro x; ext; exact ((Submodule.mem_bot ℂ).mp x.2.1).symm; rfl
        right_inv := by intro x; rfl
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    exact e.finrank_eq.trans cyc_regular_eigen_ranks.1
  · rw [ht, inf_idem, inf_comm, hi]
    let P := Module.End.eigenspace (cyc_rotation.baseChange ℂ) (-Complex.I)
    let e : ↥(P.prod (⊥ : Submodule ℂ (ℂ ⊗[ℚ] cyc_Field 4))) ≃ₗ[ℂ] P :=
      { toFun := fun x => ⟨x.1.1, x.2.1⟩
        invFun := fun x => ⟨(x.1, 0), ⟨x.2, Submodule.zero_mem _⟩⟩
        left_inv := by intro x; ext; rfl; exact ((Submodule.mem_bot ℂ).mp x.2.2).symm
        right_inv := by intro x; rfl
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    exact e.finrank_eq.trans cyc_regular_eigen_ranks.2

/-- A positive-rank balanced cyclotomic action on the CM product Hodge model.
Source: the product of the two opposite Q(i)-CM elliptic types, Silverman, Chapter II. -/
def cyc_productAction : cyc_Action cyc_productHodge 4 1 where
  cyc_order := by norm_num
  cyc_positive := by norm_num
  cyc_coordinates := cyc_productCoordinates
  cyc_preserves := cyc_product_preserves
  cyc_signature := cyc_product_signature

example : Nonempty (cyc_Action cyc_productHodge 4 1) := ⟨cyc_productAction⟩

example : Function.Injective (cyc_rep cyc_productCoordinates) :=
  (cyc_rep cyc_productCoordinates).injective

/-- The field module transported by the specified action.
Source: G32 v0.16, Section 4.1, H^1 as a free F-module. -/
@[instance_reducible] def cyc_module {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) : Module (cyc_Field m) V :=
  Module.compHom V (cyc_rep e).toRingHom

/-- The same free coordinates, now linear over the cyclotomic field.
Source: G32 v0.16, Section 4.1, the F-rank h. -/
def cyc_freeCoordinates {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    letI := cyc_module e
    V ≃ₗ[cyc_Field m] (Fin h → cyc_Field m) :=
  letI := cyc_module e
  { e.toAddEquiv with
    map_smul' := by
      intro a v
      change e (e.symm (fun i => a * e v i)) = a • e v
      rw [e.apply_symm_apply]
      rfl }

example {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    letI := cyc_module e
    Module.Free (cyc_Field m) V :=
  letI := cyc_module e
  Module.Free.of_equiv (cyc_freeCoordinates e).symm

example {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ}
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (v : V) : cyc_freeCoordinates e v = e v := rfl

example : letI := cyc_module cyc_productCoordinates
    Module.finrank (cyc_Field 4) (cyc_Field 4 × cyc_Field 4) = 2 := by
  let := cyc_module cyc_productCoordinates
  rw [(cyc_freeCoordinates cyc_productCoordinates).finrank_eq]
  exact Module.finrank_fin_fun (cyc_Field 4)

example : Function.Injective
    (fun j : Fin 4 => cyc_rep cyc_productCoordinates (cyc_i ^ j.val)) := by
  intro i j hij
  apply Fin.ext
  exact (IsCyclotomicExtension.zeta_spec 4 ℚ (cyc_Field 4)).pow_inj i.isLt j.isLt
    ((cyc_rep cyc_productCoordinates).injective hij)

example : cyc_productHodge.H (2, 0) = ⊥ :=
  cyc_productHodge.supported (2, 0) (by norm_num)

end HodgeLean.Foundations
