import HodgeLean.Foundations.HodgeGroupAlgebraicDefs
import HodgeLean.Foundations.HodgeGroupAlgebraicDim
import HodgeLean.Foundations.HodgeGroupAlgebraicGalois

/-! # The Lie algebra of the constructed Hodge group (Track G2)

`g2l_lie_hodgeGroup`: in the basis `1 ⊗ b`, the tangent space at `1` of `g2_hodgeGroup H hH b`
is the complex span of `hodgeLieAlgebra H hH`.

* The Hodge decomposition gives a frame (`g2l_hodgeQ`, weights `p - q`) whose torus contains the
  circle image and lies in the Hodge group (`g2l_torusGL_mem_hodgeGroup`).
* `⊇` (`g2l_span_hodgeLie_le`): the tangent space is `Aut(ℂ)`-stable, hence spanned by rational
  matrices, and its rational points form a rational Lie algebra whose complexification contains
  the grading operator.
* `⊆` (`g2l_ringKrullDim_hodgeGroup_le`): products of the `Aut(ℂ)`-conjugate tori have
  dimension at most `dim 𝔥`; one of largest dimension has a closure that is an `Aut(ℂ)`-stable,
  hence `ℚ`-closed, subgroup containing the circle image, so it contains the Hodge group. With
  `g1_finrank_lie_eq_krullDim`, the two spaces have the same dimension.

Sources: Borel, *Linear Algebraic Groups*, 2nd ed., §2.2, §7.1–7.6 and AG.14; Moonen, *An
introduction to Mumford–Tate groups* (2004), §1–2; Deligne, *Théorie de Hodge II*, §2.1.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace HodgeLean.Foundations

open MvPolynomial HodgeLean.Foundations.Program
open scoped TensorProduct

section Frame

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)

/-- The projection of `ℂ ⊗ V` onto the Hodge piece `H (p, q)` along the other pieces.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §2.1 (the Hodge decomposition). -/
def g2l_proj (pq : ℤ × ℤ) : Module.End ℂ (ℂ ⊗[ℚ] V) :=
  (H pq).subtype ∘ₗ DirectSum.component ℂ (ℤ × ℤ) (fun i => H i) pq ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap H) hH).symm.toLinearMap

example : @g2l_proj = @g2l_proj := rfl

theorem g2l_proj_apply_of_mem (pq : ℤ × ℤ) {pq' : ℤ × ℤ} {x : ℂ ⊗[ℚ] V} (hx : x ∈ H pq') :
    g2l_proj H hH pq x = if pq' = pq then x else 0 := by
  have h : (LinearEquiv.ofBijective (DirectSum.coeLinearMap H) hH).symm x =
      DirectSum.lof ℂ (ℤ × ℤ) (fun i => H i) pq' ⟨x, hx⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact (DirectSum.coeLinearMap_of H pq' ⟨x, hx⟩).symm
  simp only [g2l_proj, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h]
  split_ifs with hpq
  · subst hpq
    rw [DirectSum.component.lof_self]
    rfl
  · rw [DirectSum.component.of]
    simp [hpq]

include hH in
theorem g2l_supp_finite {n : ℕ} (b : Module.Basis (Fin n) ℚ V) : {pq | H pq ≠ ⊥}.Finite := by
  have : Module.Finite ℂ (ℂ ⊗[ℚ] V) :=
    Module.Finite.of_basis (Algebra.TensorProduct.basis ℂ b)
  let := (DirectSum.IsInternal.submodule_iSupIndep hH).fintypeNeBotOfFiniteDimensional
  exact Set.finite_coe_iff.mp (by exact Finite.of_fintype {i // H i ≠ ⊥})

variable {n : ℕ} (b : Module.Basis (Fin n) ℚ V)

/-- The pairs `(p, q)` with `H (p, q) ≠ 0`.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §2.1. -/
def g2l_supp : Finset (ℤ × ℤ) := (g2l_supp_finite H hH b).toFinset

example : @g2l_supp = @g2l_supp := rfl

theorem g2l_mem_supp {pq : ℤ × ℤ} : pq ∈ g2l_supp H hH b ↔ H pq ≠ ⊥ := by
  simp [g2l_supp]

/-- A sum over the support, evaluated on an element of a piece. -/
theorem g2l_sum_supp_apply {pq : ℤ × ℤ} {x : ℂ ⊗[ℚ] V} (hx : x ∈ H pq) (c : ℤ × ℤ → ℂ) :
    (∑ i : g2l_supp H hH b, c i.1 • g2l_proj H hH i.1) x = c pq • x := by
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, g2l_proj_apply_of_mem H hH _ hx]
  by_cases hpq : pq ∈ g2l_supp H hH b
  · rw [Finset.sum_eq_single (⟨pq, hpq⟩ : g2l_supp H hH b)]
    · simp
    · intro i _ hi
      rw [ite_eq_right (fun h => hi (Subtype.ext h.symm)), smul_zero]
    · simp
  · have hbot : H pq = ⊥ := by
      by_contra h
      exact hpq ((g2l_mem_supp H hH b).mpr h)
    have hx0 : x = 0 := by
      rw [hbot] at hx
      exact (Submodule.mem_bot ℂ).mp hx
    simp [hx0]

theorem g2l_sum_proj :
    ∑ i : g2l_supp H hH b, g2l_proj H hH i.1 = (1 : Module.End ℂ (ℂ ⊗[ℚ] V)) := by
  refine linearMap_ext_of_isInternal hH fun pq x hx => ?_
  have := g2l_sum_supp_apply H hH b hx (fun _ => 1)
  simp only [one_smul] at this
  rw [this, Module.End.one_apply]

theorem g2l_proj_mul (i j : g2l_supp H hH b) :
    g2l_proj H hH i.1 * g2l_proj H hH j.1 = if i = j then g2l_proj H hH i.1 else 0 := by
  refine linearMap_ext_of_isInternal hH fun pq x hx => ?_
  rw [Module.End.mul_apply, g2l_proj_apply_of_mem H hH _ hx]
  by_cases h1 : pq = j.1
  · rw [ite_eq_left h1, g2l_proj_apply_of_mem H hH _ hx]
    by_cases h2 : i = j
    · subst h2
      simp [g2l_proj_apply_of_mem H hH _ hx, h1]
    · have : pq ≠ i.1 := fun h => h2 (Subtype.ext (h.symm.trans h1))
      simp [h2, this]
  · rw [ite_eq_right h1, map_zero]
    by_cases h2 : i = j
    · subst h2
      simp [g2l_proj_apply_of_mem H hH _ hx, h1]
    · simp [h2]

theorem g2l_circleAction_eq (z : Circle) :
    g2_circleAction H hH z =
      ∑ i : g2l_supp H hH b, ((z : ℂ) ^ (i.1.1 - i.1.2)) • g2l_proj H hH i.1 := by
  refine linearMap_ext_of_isInternal hH fun pq x hx => ?_
  rw [g2l_sum_supp_apply H hH b hx (fun pq => (z : ℂ) ^ (pq.1 - pq.2))]
  obtain ⟨p, q⟩ := pq
  exact g2_circleAction_apply_of_mem H hH z hx

theorem g2l_gradingOperator_eq :
    gradingOperator H hH =
      ∑ i : g2l_supp H hH b, (Complex.I * ((i.1.1 : ℂ) - i.1.2)) • g2l_proj H hH i.1 := by
  refine linearMap_ext_of_isInternal hH fun pq x hx => ?_
  rw [g2l_sum_supp_apply H hH b hx (fun pq => Complex.I * ((pq.1 : ℂ) - pq.2))]
  obtain ⟨p, q⟩ := pq
  exact gradingOperator_apply_of_mem H hH hx

/-- The Hodge frame: the matrices of the projections onto the Hodge pieces, in the basis
`1 ⊗ b`.
Source: Moonen, *An introduction to Mumford–Tate groups* (2004), §1 (`h` diagonalized by the Hodge decomposition). -/
def g2l_hodgeQ (i : g2l_supp H hH b) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b) (Algebra.TensorProduct.basis ℂ b)
    (g2l_proj H hH i.1)

example : @g2l_hodgeQ = @g2l_hodgeQ := rfl

/-- The weights `p - q` of the Hodge frame.
Source: Moonen, *An introduction to Mumford–Tate groups* (2004), §1 (the weights `p - q` of `h` on `U(1)`). -/
def g2l_hodgeW (i : g2l_supp H hH b) : ℤ := i.1.1 - i.1.2

example : @g2l_hodgeW = @g2l_hodgeW := rfl

theorem g2l_isFrame_hodgeQ : g2l_IsFrame (g2l_hodgeQ H hH b) := by
  refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
  · rw [g2l_hodgeQ, ← LinearMap.toMatrix_mul, g2l_proj_mul, ite_eq_left rfl]
  · rw [g2l_hodgeQ, g2l_hodgeQ, ← LinearMap.toMatrix_mul, g2l_proj_mul, ite_eq_right hij, map_zero]
  · simp only [g2l_hodgeQ]
    rw [← map_sum, g2l_sum_proj, LinearMap.toMatrix_one]

theorem g2l_toMatrix_circleAction (z : Circle) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b) (Algebra.TensorProduct.basis ℂ b)
      (g2_circleAction H hH z) =
      g2l_torusAt (g2l_hodgeQ H hH b) (g2l_hodgeW H hH b) (Circle.toUnits z) := by
  rw [g2l_circleAction_eq H hH b, map_sum, g2l_torusAt]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, g2l_hodgeQ, g2l_hodgeW, Units.val_zpow_eq_zpow_val, Circle.toUnits_apply]
  rfl

theorem g2l_toMatrix_gradingOperator :
    LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b) (Algebra.TensorProduct.basis ℂ b)
      (gradingOperator H hH) = Complex.I • g2l_frameD (g2l_hodgeQ H hH b) (g2l_hodgeW H hH b) := by
  rw [g2l_gradingOperator_eq H hH b, map_sum, g2l_frameD, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_smul, g2l_hodgeQ, g2l_hodgeW]
  push_cast
  rfl

end Frame

section Galois

variable {n : ℕ}

theorem g2l_coords_map (σ : RingAut ℂ) (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    g1_coords (Matrix.GeneralLinearGroup.map (σ : ℂ →+* ℂ) g) = fun ab => σ (g1_coords g ab) :=
  rfl

/-- A field automorphism of `ℂ` commutes with evaluating a rational polynomial. -/
theorem g2l_aeval_coords_map (σ : RingAut ℂ) (g : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (f : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (g1_coords (Matrix.GeneralLinearGroup.map (σ : ℂ →+* ℂ) g)) f =
      σ (aeval (g1_coords g) f) := by
  rw [aeval_def, aeval_def, ← RingEquiv.coe_toRingHom, eval₂_comp_left]
  congr 1
  exact RingHom.ext_rat _ _

/-- A zero set of rational polynomials is stable under `Aut(ℂ)`. -/
theorem g2l_map_mem_ratZeroSet (σ : RingAut ℂ) {S : Set (MvPolynomial (Fin n × Fin n) ℚ)}
    {g : Matrix.GeneralLinearGroup (Fin n) ℂ} (hg : g ∈ g2_ratZeroSet S) :
    Matrix.GeneralLinearGroup.map (σ : ℂ →+* ℂ) g ∈ g2_ratZeroSet S := fun f hf => by
  rw [g2l_aeval_coords_map, hg f hf, map_zero]

end Galois

section HodgeGroup

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
  {n : ℕ} (b : Module.Basis (Fin n) ℚ V)

/-- The rational equations of the Hodge group: those vanishing on some `ℚ`-algebraic subgroup
containing the circle image.
Source: Moonen, *An introduction to Mumford–Tate groups* (2004), §1–2; Borel, *Linear Algebraic Groups*, 2nd ed., AG.11.3. -/
def g2l_hgEquations : Set (MvPolynomial (Fin n × Fin n) ℚ) :=
  {f | ∃ G, (g2_IsRatAlgSubgroup G ∧ g2_circleImage H hH b ⊆ G) ∧
    ∀ g ∈ G, aeval (g1_coords g) f = 0}

example : @g2l_hgEquations = @g2l_hgEquations := rfl

theorem g2l_hodgeGroup_eq_ratZeroSet :
    g2_hodgeGroup H hH b = g2_ratZeroSet (g2l_hgEquations H hH b) := by
  ext g
  constructor
  · rintro hg f ⟨G, hG, hfG⟩
    exact hfG g (hg G hG)
  · intro hg G hG
    obtain ⟨⟨S, rfl⟩, -⟩ := hG.1
    exact fun f hf => hg f ⟨_, hG, fun g' hg' => hg' f hf⟩

theorem g2l_hodgeGroup_map (σ : RingAut ℂ) {g : Matrix.GeneralLinearGroup (Fin n) ℂ}
    (hg : g ∈ g2_hodgeGroup H hH b) :
    Matrix.GeneralLinearGroup.map (σ : ℂ →+* ℂ) g ∈ g2_hodgeGroup H hH b := by
  rw [g2l_hodgeGroup_eq_ratZeroSet] at hg ⊢
  exact g2l_map_mem_ratZeroSet σ hg

theorem g2l_hodgeGroup_one : (1 : Matrix.GeneralLinearGroup (Fin n) ℂ) ∈ g2_hodgeGroup H hH b :=
  fun _ hG => hG.1.2.1

theorem g2l_hodgeGroup_mul {g h : Matrix.GeneralLinearGroup (Fin n) ℂ}
    (hg : g ∈ g2_hodgeGroup H hH b) (hh : h ∈ g2_hodgeGroup H hH b) :
    g * h ∈ g2_hodgeGroup H hH b :=
  fun G hG => hG.1.2.2.1 g (hg G hG) h (hh G hG)

theorem g2l_hodgeGroup_inv {g : Matrix.GeneralLinearGroup (Fin n) ℂ}
    (hg : g ∈ g2_hodgeGroup H hH b) : g⁻¹ ∈ g2_hodgeGroup H hH b :=
  fun G hG => hG.1.2.2.2 g (hg G hG)

/-- The Hodge group as a subgroup of `GL_n(ℂ)`.
Source: Mumford, *Families of abelian varieties*, Proc. Sympos. Pure Math. 9 (1966), §1. -/
def g2l_hodgeSubgroup : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ) where
  carrier := g2_hodgeGroup H hH b
  one_mem' := g2l_hodgeGroup_one H hH b
  mul_mem' := g2l_hodgeGroup_mul H hH b
  inv_mem' := g2l_hodgeGroup_inv H hH b

example : @g2l_hodgeSubgroup = @g2l_hodgeSubgroup := rfl

/-- The circle `U(1)` has infinitely many points. -/
theorem g2l_infinite_circle : (Set.range Circle.toUnits).Infinite := by
  have h1 : (Set.Icc (0 : ℝ) 1).Infinite := Set.Icc_infinite (by norm_num)
  have h2 : Set.InjOn Circle.exp (Set.Icc (0 : ℝ) 1) :=
    Circle.exp_injOn_Icc (by linarith [Real.pi_gt_three])
  have h3 := h1.image h2
  have hinj : Function.Injective Circle.toUnits := fun z z' h => by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h
    simp only [Circle.toUnits_apply, Units.val_mk0] at this
    exact Subtype.ext this
  refine (h3.image hinj.injOn).mono ?_
  rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
  exact ⟨_, rfl⟩

theorem g2l_torusGL_circle (z : Circle) :
    g2l_torusGL (g2l_isFrame_hodgeQ H hH b) (g2l_hodgeW H hH b) (Circle.toUnits z) ∈
      g2_circleImage H hH b :=
  ⟨z, by rw [g2l_torusGL_val, g2l_toMatrix_circleAction]⟩

/-- **The whole torus of the Hodge frame lies in the Hodge group**: a rational equation of a
`ℚ`-algebraic subgroup containing the circle image vanishes at infinitely many torus points,
hence on the torus. -/
theorem g2l_torusGL_mem_hodgeGroup (t : ℂˣ) :
    g2l_torusGL (g2l_isFrame_hodgeQ H hH b) (g2l_hodgeW H hH b) t ∈ g2_hodgeGroup H hH b := by
  intro G hG
  obtain ⟨⟨S, hS⟩, -⟩ := hG.1
  rw [hS]
  intro f hf
  have hfG : ∀ g ∈ G, aeval (g1_coords g) f = 0 := by
    intro g hg
    rw [hS] at hg
    exact hg f hf
  have key := g2l_torus_vanish_of_infinite (g2l_isFrame_hodgeQ H hH b) (g2l_hodgeW H hH b)
    (MvPolynomial.map (algebraMap ℚ ℂ) f) g2l_infinite_circle (by
      rintro _ ⟨z, rfl⟩
      rw [eval_map, ← aeval_def]
      exact hfG _ (hG.2 (g2l_torusGL_circle H hH b z))) t
  rwa [eval_map, ← aeval_def] at key

end HodgeGroup

section RatSpan

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ} (b : Module.Basis (Fin n) ℚ V)

/-- The complex matrix, in the basis `1 ⊗ b`, of the base change of a rational endomorphism.
Source: Bourbaki, *Algèbre*, ch. II (matrix of an endomorphism in the base-changed basis). -/
def g2l_ratMat (X : Module.End ℚ V) : Matrix (Fin n) (Fin n) ℂ :=
  (LinearMap.toMatrix b b X).map (algebraMap ℚ ℂ)

example : @g2l_ratMat = @g2l_ratMat := rfl

theorem g2l_map_complexSpan (W : Submodule ℚ (Module.End ℚ V)) :
    (complexSpan W).map (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
      (Algebra.TensorProduct.basis ℂ b)).toLinearMap =
      Submodule.span ℂ (g2l_ratMat b '' W) := by
  rw [complexSpan, Submodule.map_span, ← Set.image_comp]
  congr 1
  refine Set.image_congr fun X _ => ?_
  simp only [Function.comp_apply, LinearEquiv.coe_coe, LinearMap.toMatrix_baseChange, g2l_ratMat]

theorem g2l_ratMat_mul (X Y : Module.End ℚ V) :
    g2l_ratMat b (X * Y) = g2l_ratMat b X * g2l_ratMat b Y := by
  rw [g2l_ratMat, g2l_ratMat, g2l_ratMat, LinearMap.toMatrix_mul, Matrix.map_mul]

theorem g2l_ratMat_sub (X Y : Module.End ℚ V) :
    g2l_ratMat b (X - Y) = g2l_ratMat b X - g2l_ratMat b Y := by
  rw [g2l_ratMat, g2l_ratMat, g2l_ratMat, map_sub, Matrix.map_sub _ (map_sub _)]

theorem g2l_ratMat_map (σ : RingAut ℂ) (X : Module.End ℚ V) :
    (g2l_ratMat b X).map σ = g2l_ratMat b X := by
  rw [g2l_ratMat, Matrix.map_map]
  congr 1
  funext q
  exact map_ratCast σ q

/-- A span of rational matrices is stable under `Aut(ℂ)`. -/
theorem g2l_map_mem_span_ratMat (σ : RingAut ℂ) {T : Set (Module.End ℚ V)}
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ Submodule.span ℂ (g2l_ratMat b '' T)) :
    Y.map σ ∈ Submodule.span ℂ (g2l_ratMat b '' T) := by
  induction hY using Submodule.span_induction with
  | mem Y hY =>
    obtain ⟨X, hX, rfl⟩ := hY
    rw [g2l_ratMat_map]
    exact Submodule.subset_span ⟨X, hX, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add σ)]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [Matrix.map_smul' _ _ _ (map_mul σ)]
    exact Submodule.smul_mem _ _ hx

attribute [local instance 100] LieRing.ofAssociativeRing in
/-- The complex span of the matrices of a rational Lie subalgebra is closed under commutators. -/
theorem g2l_commutator_mem_span_ratMat (L : LieSubalgebra ℚ (Module.End ℚ V))
    {Y Y' : Matrix (Fin n) (Fin n) ℂ}
    (hY : Y ∈ Submodule.span ℂ (g2l_ratMat b '' (L : Set (Module.End ℚ V))))
    (hY' : Y' ∈ Submodule.span ℂ (g2l_ratMat b '' (L : Set (Module.End ℚ V)))) :
    Y * Y' - Y' * Y ∈ Submodule.span ℂ (g2l_ratMat b '' (L : Set (Module.End ℚ V))) := by
  set Sp := Submodule.span ℂ (g2l_ratMat b '' (L : Set (Module.End ℚ V)))
  have hgen : ∀ X ∈ L, ∀ Y' ∈ Sp, g2l_ratMat b X * Y' - Y' * g2l_ratMat b X ∈ Sp := by
    intro X hX Y' hY'
    induction hY' using Submodule.span_induction with
    | mem Y' hY' =>
      obtain ⟨X', hX', rfl⟩ := hY'
      rw [← g2l_ratMat_mul, ← g2l_ratMat_mul, ← g2l_ratMat_sub]
      refine Submodule.subset_span ⟨_, ?_, rfl⟩
      have := L.lie_mem hX hX'
      rwa [Ring.lie_def] at this
    | zero => simp
    | add x y _ _ hx hy =>
      have : g2l_ratMat b X * (x + y) - (x + y) * g2l_ratMat b X =
          (g2l_ratMat b X * x - x * g2l_ratMat b X) + (g2l_ratMat b X * y - y * g2l_ratMat b X) := by
        noncomm_ring
      rw [this]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
      exact Submodule.smul_mem _ _ hx
  induction hY using Submodule.span_induction with
  | mem Y hY =>
    obtain ⟨X, hX, rfl⟩ := hY
    exact hgen X hX Y' hY'
  | zero => simp
  | add x y _ _ hx hy =>
    have : (x + y) * Y' - Y' * (x + y) = (x * Y' - Y' * x) + (y * Y' - Y' * y) := by
      noncomm_ring
    rw [this]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
    exact Submodule.smul_mem _ _ hx

end RatSpan

section LieGalois

variable {n : ℕ}

theorem g2l_eval_map_symm (σ : RingAut ℂ) (x : Fin n × Fin n → ℂ)
    (p : MvPolynomial (Fin n × Fin n) ℂ) :
    eval x (MvPolynomial.map ((σ.symm : RingAut ℂ) : ℂ →+* ℂ) p) =
      σ.symm (eval (fun ab => σ (x ab)) p) := by
  rw [eval_map]
  have := eval₂_comp_left ((σ.symm : RingAut ℂ) : ℂ →+* ℂ) (RingHom.id ℂ) (fun ab => σ (x ab)) p
  rw [show eval (fun ab => σ (x ab)) p = eval₂ (RingHom.id ℂ) (fun ab => σ (x ab)) p from rfl]
  change _ = ((σ.symm : RingAut ℂ) : ℂ →+* ℂ) _
  rw [this]
  congr 1
  funext ab
  simp

/-- The tangent space at `1` of an `Aut(ℂ)`-stable set is `Aut(ℂ)`-stable. -/
theorem g2l_lieOfSet_map {S : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)}
    (hS : ∀ σ : RingAut ℂ, ∀ g ∈ S, Matrix.GeneralLinearGroup.map (σ : ℂ →+* ℂ) g ∈ S)
    (σ : RingAut ℂ) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ g1_lieOfSet S) :
    Y.map σ ∈ g1_lieOfSet S := by
  refine g1_mem_lieOfSet_iff.mpr fun f hf => ?_
  set f' := MvPolynomial.map ((σ.symm : RingAut ℂ) : ℂ →+* ℂ) f
  have hf' : f' ∈ g1_vanishingIdealSet S := by
    refine g1_mem_vanishingIdealSet_iff.mpr fun g hg => ?_
    rw [g2l_eval_map_symm]
    have := g1_mem_vanishingIdealSet_iff.mp hf _ (hS σ g hg)
    rw [g2l_coords_map] at this
    rw [this, map_zero]
  have h0 := g1_mem_lieOfSet_iff.mp hY f' hf'
  have h1 : ∀ ab : Fin n × Fin n, eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) ℂ))
      (pderiv ab f') = σ.symm (eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) ℂ))
        (pderiv ab f)) := by
    intro ab
    rw [pderiv_map, g2l_eval_map_symm]
    have : (fun cd => σ (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) ℂ) cd)) =
        g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) ℂ) := by
      funext cd
      simp only [g1_coords, Units.val_one, Matrix.one_apply]
      split_ifs <;> simp
    rw [this]
  rw [g1_differential_apply_dir] at h0 ⊢
  simp only [h1] at h0
  have := congrArg σ h0
  rw [map_sum, map_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [map_mul, RingEquiv.apply_symm_apply, Matrix.map_apply]

end LieGalois

section Supset

attribute [local instance 100] LieRing.ofAssociativeRing

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
  {n : ℕ} (b : Module.Basis (Fin n) ℚ V)

/-- The rational Lie subalgebra of endomorphisms whose matrices lie in a tangent space that is
closed under products.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.14.2 (the `k`-structure of a `k`-closed set) and §3.5. -/
def g2l_ratLie (S : Set (Matrix.GeneralLinearGroup (Fin n) ℂ))
    (hS : ∀ g ∈ S, ∀ h ∈ S, g * h ∈ S) : LieSubalgebra ℚ (Module.End ℚ V) where
  carrier := {X : Module.End ℚ V | g2l_ratMat b X ∈ g1_lieOfSet S}
  add_mem' {X Y} hX hY := by
    change g2l_ratMat b (X + Y) ∈ g1_lieOfSet S
    rw [g2l_ratMat, map_add, Matrix.map_add _ (map_add _)]
    exact add_mem hX hY
  zero_mem' := by
    change g2l_ratMat b 0 ∈ g1_lieOfSet S
    rw [g2l_ratMat, map_zero, Matrix.map_zero _ (map_zero _)]
    exact Submodule.zero_mem _
  smul_mem' q {X} hX := by
    change g2l_ratMat b (q • X) ∈ g1_lieOfSet S
    rw [g2l_ratMat, map_smul, Matrix.map_smul' _ _ _ (map_mul _)]
    exact Submodule.smul_mem _ _ hX
  lie_mem' {X Y} hX hY := by
    change g2l_ratMat b ⁅X, Y⁆ ∈ g1_lieOfSet S
    rw [Ring.lie_def, g2l_ratMat_sub, g2l_ratMat_mul, g2l_ratMat_mul]
    exact g1_lieOfSet_bracket_mem S hS _ _ hX hY

example : @g2l_ratLie = @g2l_ratLie := rfl

theorem g2l_ratMat_toLin (R : Matrix (Fin n) (Fin n) ℚ) :
    g2l_ratMat b (Matrix.toLin b b R) = R.map (algebraMap ℚ ℂ) := by
  rw [g2l_ratMat, LinearMap.toMatrix_toLin]

/-- **The Lie algebra of the Hodge group contains the complexified Hodge Lie algebra.** The
tangent space of the Hodge group is `Aut(ℂ)`-stable, hence spanned by rational matrices (Galois
descent), so its rational points form a rational Lie algebra whose complexification contains
the grading operator; minimality of `hodgeLieAlgebra` does the rest. -/
theorem g2l_span_hodgeLie_le :
    Submodule.span ℂ (g2l_ratMat b '' ((hodgeLieAlgebra H hH : LieSubalgebra ℚ _) :
      Set (Module.End ℚ V))) ≤ g1_lieOfSet (g2_hodgeGroup H hH b) := by
  have : FiniteDimensional ℚ V := Module.Finite.of_basis b
  set Hg := g2_hodgeGroup H hH b
  have hmul : ∀ g ∈ Hg, ∀ h ∈ Hg, g * h ∈ Hg := fun g hg h hh => g2l_hodgeGroup_mul H hH b hg hh
  set 𝔪 := g2l_ratLie b Hg hmul
  have hD : g2l_frameD (g2l_hodgeQ H hH b) (g2l_hodgeW H hH b) ∈ g1_lieOfSet Hg :=
    g2l_frameD_mem_lieOfSet _ _ fun t => g2l_torusGL_mem_hodgeGroup H hH b t
  have hC : LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
      (Algebra.TensorProduct.basis ℂ b) (gradingOperator H hH) ∈ g1_lieOfSet Hg := by
    rw [g2l_toMatrix_gradingOperator]
    exact Submodule.smul_mem _ _ hD
  have hdesc := g2l_matrix_descent (g1_lieOfSet Hg)
    (fun (σ : RingAut ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) hY =>
      g2l_lieOfSet_map (fun σ g hg => g2l_hodgeGroup_map H hH b σ hg) σ hY) hC
  have hspan : Submodule.span ℂ {Z | Z ∈ g1_lieOfSet Hg ∧
      ∃ R : Matrix (Fin n) (Fin n) ℚ, R.map (algebraMap ℚ ℂ) = Z} ≤
      Submodule.span ℂ (g2l_ratMat b '' (𝔪 : Set (Module.End ℚ V))) := by
    refine Submodule.span_mono ?_
    rintro Z ⟨hZ, R, rfl⟩
    refine ⟨Matrix.toLin b b R, ?_, g2l_ratMat_toLin b R⟩
    change g2l_ratMat b (Matrix.toLin b b R) ∈ g1_lieOfSet Hg
    rw [g2l_ratMat_toLin]
    exact hZ
  have hCm : gradingOperator H hH ∈ complexSpan 𝔪.toSubmodule := by
    have h1 := hspan hdesc
    have h2 : Submodule.span ℂ (g2l_ratMat b '' (𝔪 : Set (Module.End ℚ V))) =
        (complexSpan 𝔪.toSubmodule).map (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
          (Algebra.TensorProduct.basis ℂ b)).toLinearMap := (g2l_map_complexSpan b _).symm
    rw [h2] at h1
    obtain ⟨C', hC', heq⟩ := h1
    have := (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
      (Algebra.TensorProduct.basis ℂ b)).injective heq
    rw [← this]
    exact hC'
  have hle : hodgeLieAlgebra H hH ≤ 𝔪 := rationalLieHull_le hCm
  rw [Submodule.span_le]
  rintro _ ⟨X, hX, rfl⟩
  exact hle hX

end Supset

section Lists

open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
  {n : ℕ} (b : Module.Basis (Fin n) ℚ V)

/-- The conjugate of the Hodge frame under a field automorphism of `ℂ`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.14.1 (Galois conjugates). -/
def g2l_sigmaQ (σ : RingAut ℂ) (i : g2l_supp H hH b) : Matrix (Fin n) (Fin n) ℂ :=
  (g2l_hodgeQ H hH b i).map σ

example : @g2l_sigmaQ = @g2l_sigmaQ := rfl

theorem g2l_isFrame_sigmaQ (σ : RingAut ℂ) : g2l_IsFrame (g2l_sigmaQ H hH b σ) :=
  (g2l_isFrame_hodgeQ H hH b).map (σ : ℂ →+* ℂ)

/-- The torus of a conjugate frame.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.14.1 and §8.5. -/
def g2l_sigmaTorus (σ : RingAut ℂ) : Set (Matrix.GeneralLinearGroup (Fin n) ℂ) :=
  Set.range (g2l_torusGL (g2l_isFrame_sigmaQ H hH b σ) (g2l_hodgeW H hH b))

example : @g2l_sigmaTorus = @g2l_sigmaTorus := rfl

theorem g2l_map_torusGL (σ : RingAut ℂ) {Q : g2l_supp H hH b → Matrix (Fin n) (Fin n) ℂ}
    (hQ : g2l_IsFrame Q) (t : ℂˣ) :
    Matrix.GeneralLinearGroup.map (σ : ℂ →+* ℂ) (g2l_torusGL hQ (g2l_hodgeW H hH b) t) =
      g2l_torusGL (hQ.map (σ : ℂ →+* ℂ)) (g2l_hodgeW H hH b)
        (Units.map ((σ : ℂ →+* ℂ) : ℂ →* ℂ) t) := by
  ext a c
  rw [Matrix.GeneralLinearGroup.map_apply, g2l_torusGL_val, g2l_torusGL_val]
  have := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M a c)
    (g2l_torusAt_map (Q := Q) (g2l_hodgeW H hH b) (σ : ℂ →+* ℂ) t)
  simpa using this

theorem g2l_sigmaTorus_subset (σ : RingAut ℂ) :
    g2l_sigmaTorus H hH b σ ⊆ g2_hodgeGroup H hH b := by
  rintro _ ⟨t, rfl⟩
  have h := g2l_map_torusGL H hH b σ (g2l_isFrame_hodgeQ H hH b)
    (Units.map ((σ.symm : RingAut ℂ) : ℂ →* ℂ) t)
  have ht : Units.map ((σ : ℂ →+* ℂ) : ℂ →* ℂ) (Units.map ((σ.symm : RingAut ℂ) : ℂ →* ℂ) t) =
      t := by
    ext; simp
  rw [ht] at h
  change g2l_torusGL ((g2l_isFrame_hodgeQ H hH b).map (σ : ℂ →+* ℂ)) _ t ∈ _
  rw [← h]
  exact g2l_hodgeGroup_map H hH b σ (g2l_torusGL_mem_hodgeGroup H hH b _)

theorem g2l_map_sigmaTorus (σ τ : RingAut ℂ) {g : Matrix.GeneralLinearGroup (Fin n) ℂ}
    (hg : g ∈ g2l_sigmaTorus H hH b τ) :
    Matrix.GeneralLinearGroup.map (σ : ℂ →+* ℂ) g ∈ g2l_sigmaTorus H hH b (τ.trans σ) := by
  obtain ⟨t, rfl⟩ := hg
  rw [g2l_map_torusGL H hH b σ (g2l_isFrame_sigmaQ H hH b τ)]
  refine ⟨Units.map ((σ : ℂ →+* ℂ) : ℂ →* ℂ) t, ?_⟩
  ext a c
  rw [g2l_torusGL_val, g2l_torusGL_val]
  congr 2

/-- The frames `σ_l Q` of a list of automorphisms.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §2.2. -/
def g2l_QsL (L : List (RingAut ℂ)) (l : Fin L.length) :
    g2l_supp H hH b → Matrix (Fin n) (Fin n) ℂ :=
  g2l_sigmaQ H hH b (L.get l)

example : @g2l_QsL = @g2l_QsL := rfl

theorem g2l_isFrame_QsL (L : List (RingAut ℂ)) (l : Fin L.length) :
    g2l_IsFrame (g2l_QsL H hH b L l) :=
  g2l_isFrame_sigmaQ H hH b _

/-- The products `σ_1(T) ⋯ σ_N(T)` of the conjugate tori of a list of automorphisms.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §2.2 (finite products of conjugate tori). -/
def g2l_GammaL (L : List (RingAut ℂ)) : Set (Matrix.GeneralLinearGroup (Fin n) ℂ) :=
  g2l_Gamma (g2l_hodgeW H hH b) (g2l_isFrame_QsL H hH b L)

example : @g2l_GammaL = @g2l_GammaL := rfl

theorem g2l_GammaL_eq (L : List (RingAut ℂ)) :
    g2l_GammaL H hH b L = (L.map (g2l_sigmaTorus H hH b)).prod := by
  induction L with
  | nil =>
    ext g
    simp only [List.map_nil, List.prod_nil, Set.mem_one]
    constructor
    · rintro ⟨t, rfl⟩; simp [g2l_prodTorus]
    · rintro rfl; exact ⟨fun l => l.elim0, by simp [g2l_prodTorus]⟩
  | cons σ L ih =>
    rw [List.map_cons, List.prod_cons, ← ih, g2l_GammaL, g2l_Gamma_succ]
    rfl

theorem g2l_one_mem_GammaL (L : List (RingAut ℂ)) : 1 ∈ g2l_GammaL H hH b L := by
  rw [g2l_GammaL_eq]
  induction L with
  | nil => simp
  | cons σ L ih =>
    rw [List.map_cons, List.prod_cons]
    exact ⟨1, ⟨1, map_one _⟩, 1, ih, mul_one 1⟩

theorem g2l_GammaL_append (L L' : List (RingAut ℂ)) :
    g2l_GammaL H hH b (L ++ L') = g2l_GammaL H hH b L * g2l_GammaL H hH b L' := by
  rw [g2l_GammaL_eq, g2l_GammaL_eq, g2l_GammaL_eq, List.map_append, List.prod_append]

theorem g2l_GammaL_subset_append_left (L L' : List (RingAut ℂ)) :
    g2l_GammaL H hH b L ⊆ g2l_GammaL H hH b (L ++ L') := by
  rw [g2l_GammaL_append]
  intro g hg
  exact ⟨g, hg, 1, g2l_one_mem_GammaL H hH b L', mul_one g⟩

theorem g2l_GammaL_subset_append_right (L L' : List (RingAut ℂ)) :
    g2l_GammaL H hH b L' ⊆ g2l_GammaL H hH b (L ++ L') := by
  rw [g2l_GammaL_append]
  intro g hg
  exact ⟨1, g2l_one_mem_GammaL H hH b L, g, hg, one_mul g⟩

theorem g2l_GammaL_subset (L : List (RingAut ℂ)) :
    g2l_GammaL H hH b L ⊆ g2_hodgeGroup H hH b := by
  rw [g2l_GammaL_eq]
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Set.one_subset]
    exact g2l_hodgeGroup_one H hH b
  | cons σ L ih =>
    rw [List.map_cons, List.prod_cons]
    rintro _ ⟨g, hg, h, hh, rfl⟩
    exact g2l_hodgeGroup_mul H hH b (g2l_sigmaTorus_subset H hH b σ hg) (ih hh)

theorem g2l_map_mem_GammaL (σ : RingAut ℂ) (L : List (RingAut ℂ))
    {g : Matrix.GeneralLinearGroup (Fin n) ℂ} (hg : g ∈ g2l_GammaL H hH b L) :
    Matrix.GeneralLinearGroup.map (σ : ℂ →+* ℂ) g ∈
      g2l_GammaL H hH b (L.map fun τ => τ.trans σ) := by
  rw [g2l_GammaL_eq] at hg ⊢
  induction L generalizing g with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Set.mem_one] at hg ⊢
    rw [hg, map_one]
  | cons τ L ih =>
    rw [List.map_cons, List.prod_cons] at hg
    rw [List.map_cons, List.map_cons, List.prod_cons]
    obtain ⟨a, ha, c, hc, rfl⟩ := hg
    rw [map_mul]
    exact ⟨_, g2l_map_sigmaTorus H hH b σ τ ha, _, ih hc, rfl⟩

end Lists

section HodgeSpan

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
  {n : ℕ} (b : Module.Basis (Fin n) ℚ V)

/-- The complexified Hodge Lie algebra as a space of matrices in the basis `1 ⊗ b`.
Source: Moonen, *An introduction to Mumford–Tate groups* (2004), §1–2; this repository's `hodgeLieAlgebra`. -/
def g2l_hM : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  Submodule.span ℂ (g2l_ratMat b '' ((hodgeLieAlgebra H hH : LieSubalgebra ℚ _) :
    Set (Module.End ℚ V)))

example : @g2l_hM = @g2l_hM := rfl

theorem g2l_frameD_mem_hM :
    g2l_frameD (g2l_hodgeQ H hH b) (g2l_hodgeW H hH b) ∈ g2l_hM H hH b := by
  have : FiniteDimensional ℚ V := Module.Finite.of_basis b
  have hC : LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
      (Algebra.TensorProduct.basis ℂ b) (gradingOperator H hH) ∈ g2l_hM H hH b := by
    have h2 : g2l_hM H hH b = (complexSpan (hodgeLieAlgebra H hH).toSubmodule).map
        (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
          (Algebra.TensorProduct.basis ℂ b)).toLinearMap := (g2l_map_complexSpan b _).symm
    rw [h2]
    exact ⟨_, mem_complexSpan_rationalLieHull _, rfl⟩
  rw [g2l_toMatrix_gradingOperator] at hC
  have := Submodule.smul_mem _ (-Complex.I) hC
  rwa [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul] at this

theorem g2l_frameD_sigma_mem_hM (σ : RingAut ℂ) :
    g2l_frameD (g2l_sigmaQ H hH b σ) (g2l_hodgeW H hH b) ∈ g2l_hM H hH b := by
  have h := g2l_frameD_map (Q := g2l_hodgeQ H hH b) (g2l_hodgeW H hH b) (σ : ℂ →+* ℂ)
  change g2l_frameD (fun i => (g2l_hodgeQ H hH b i).map (σ : ℂ →+* ℂ)) _ ∈ _
  rw [← h]
  exact g2l_map_mem_span_ratMat b σ (g2l_frameD_mem_hM H hH b)

theorem g2l_bracket_mem_hM (σ : RingAut ℂ) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : Y ∈ g2l_hM H hH b) :
    g2l_frameD (g2l_sigmaQ H hH b σ) (g2l_hodgeW H hH b) * Y -
      Y * g2l_frameD (g2l_sigmaQ H hH b σ) (g2l_hodgeW H hH b) ∈ g2l_hM H hH b :=
  g2l_commutator_mem_span_ratMat b _ (g2l_frameD_sigma_mem_hM H hH b σ) hY

theorem g2l_GammaL_isPrime (L : List (RingAut ℂ)) :
    (g1_vanishingIdealSet (g2l_GammaL H hH b L)).IsPrime :=
  g2l_vanishingIdealSet_Gamma_isPrime _ _

theorem g2l_dim_GammaL_le (L : List (RingAut ℂ)) :
    ringKrullDim (MvPolynomial (Fin n × Fin n) ℂ ⧸ g1_vanishingIdealSet (g2l_GammaL H hH b L)) ≤
      Module.finrank ℂ (g2l_hM H hH b) :=
  g2l_ringKrullDim_Gamma_le _ (g2l_isFrame_QsL H hH b L) (g2l_hM H hH b)
    (fun _ => g2l_frameD_sigma_mem_hM H hH b _) (fun _ _ hY => g2l_bracket_mem_hM H hH b _ hY)
    (g2l_GammaL_isPrime H hH b L)

theorem g2l_dim_GammaL_nonneg (L : List (RingAut ℂ)) :
    0 ≤ ringKrullDim (MvPolynomial (Fin n × Fin n) ℂ ⧸
      g1_vanishingIdealSet (g2l_GammaL H hH b L)) := by
  have hne : g1_vanishingIdealSet (g2l_GammaL H hH b L) ≠ ⊤ := by
    intro h
    have h1 : (1 : MvPolynomial (Fin n × Fin n) ℂ) ∈ g1_vanishingIdealSet (g2l_GammaL H hH b L) :=
      h ▸ Submodule.mem_top
    have := g1_mem_vanishingIdealSet_iff.mp h1 1 (g2l_one_mem_GammaL H hH b L)
    simp at this
  have : Nontrivial (MvPolynomial (Fin n × Fin n) ℂ ⧸
      g1_vanishingIdealSet (g2l_GammaL H hH b L)) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact ringKrullDim_nonneg_of_nontrivial

end HodgeSpan

section Stable

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
  {n : ℕ} (b : Module.Basis (Fin n) ℚ V)

theorem g2l_exists_nat_of_le {x : WithBot ℕ∞} {r : ℕ} (h0 : 0 ≤ x) (h1 : x ≤ r) :
    ∃ k : ℕ, x = k ∧ k ≤ r := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd (WithBot.coe_le_coe.mp h1) (by simp)
    | coe k =>
      refine ⟨k, rfl, ?_⟩
      exact_mod_cast h1

/-- **Stabilization.** Some product of conjugate tori has a closure containing all the others:
its vanishing ideal is contained in the vanishing ideal of every product. Among the products,
take one of largest dimension (dimensions are bounded by `dim 𝔥`); appending factors gives an
irreducible set of no larger dimension containing it, hence with the same closure. -/
theorem g2l_exists_GammaL_stable : ∃ L₀ : List (RingAut ℂ),
    ringKrullDim (MvPolynomial (Fin n × Fin n) ℂ ⧸
      g1_vanishingIdealSet (g2l_GammaL H hH b L₀)) ≤ Module.finrank ℂ (g2l_hM H hH b) ∧
    ∀ L, g1_vanishingIdealSet (g2l_GammaL H hH b L₀) ≤
      g1_vanishingIdealSet (g2l_GammaL H hH b L) := by
  classical
  set r := Module.finrank ℂ (g2l_hM H hH b)
  set d : List (RingAut ℂ) → WithBot ℕ∞ := fun L => ringKrullDim
    (MvPolynomial (Fin n × Fin n) ℂ ⧸ g1_vanishingIdealSet (g2l_GammaL H hH b L))
  let Pm : ℕ → Prop := fun m => ∃ L, (m : WithBot ℕ∞) ≤ d L
  have hP0 : Pm 0 := ⟨[], by exact_mod_cast g2l_dim_GammaL_nonneg H hH b []⟩
  set m := Nat.findGreatest Pm r
  obtain ⟨L₀, hL₀⟩ : Pm m := Nat.findGreatest_spec (Nat.zero_le r) hP0
  have hle : ∀ L, d L ≤ m := by
    intro L
    obtain ⟨k, hk, hkr⟩ := g2l_exists_nat_of_le (g2l_dim_GammaL_nonneg H hH b L)
      (g2l_dim_GammaL_le H hH b L)
    change ringKrullDim _ ≤ _
    rw [hk]
    exact_mod_cast Nat.le_findGreatest (P := Pm) hkr ⟨L, hk.ge⟩
  have hd₀ : d L₀ = m := le_antisymm (hle L₀) hL₀
  refine ⟨L₀, ?_, fun L => ?_⟩
  · change d L₀ ≤ _
    rw [hd₀]
    exact_mod_cast Nat.findGreatest_le r
  set J := g1_vanishingIdealSet (g2l_GammaL H hH b (L₀ ++ L))
  have hJ₀ : J ≤ g1_vanishingIdealSet (g2l_GammaL H hH b L₀) :=
    g1_vanishingIdealSet_anti (g2l_GammaL_subset_append_left H hH b L₀ L)
  have hJL : J ≤ g1_vanishingIdealSet (g2l_GammaL H hH b L) :=
    g1_vanishingIdealSet_anti (g2l_GammaL_subset_append_right H hH b L₀ L)
  have := g2l_GammaL_isPrime H hH b (L₀ ++ L)
  have hdJ : ringKrullDim (MvPolynomial (Fin n × Fin n) ℂ ⧸ J) = m := by
    refine le_antisymm (hle _) ?_
    rw [← hd₀]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hJ₀)
      (Ideal.Quotient.factor_surjective hJ₀)
  have heq : J = g1_vanishingIdealSet (g2l_GammaL H hH b L₀) := by
    by_contra hne
    exact g1_ringKrullDim_quotient_ne_of_lt J _ (lt_of_le_of_ne hJ₀ hne) m hdJ hd₀
  rw [← heq]
  exact hJL

end Stable

section Closure

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
  {n : ℕ} (b : Module.Basis (Fin n) ℚ V) {L₀ : List (RingAut ℂ)}
  (hL₀ : ∀ L, g1_vanishingIdealSet (g2l_GammaL H hH b L₀) ≤
    g1_vanishingIdealSet (g2l_GammaL H hH b L))

include hL₀

theorem g2l_mem_I₀_iff (f : MvPolynomial (Fin n × Fin n) ℂ) :
    f ∈ g1_vanishingIdealSet (g2l_GammaL H hH b L₀) ↔
      ∀ L, ∀ g ∈ g2l_GammaL H hH b L, eval (g1_coords g) f = 0 :=
  ⟨fun hf L g hg => g1_mem_vanishingIdealSet_iff.mp (hL₀ L hf) g hg,
    fun h => g1_mem_vanishingIdealSet_iff.mpr (h L₀)⟩

theorem g2l_GammaL_subset_Z (L : List (RingAut ℂ)) :
    g2l_GammaL H hH b L ⊆ g1_zeroSet (g1_vanishingIdealSet (g2l_GammaL H hH b L₀) :
      Set (MvPolynomial (Fin n × Fin n) ℂ)) :=
  fun g hg f hf => (g2l_mem_I₀_iff H hH b hL₀ f).mp hf L g hg

theorem g2l_Z_mul_left (L : List (RingAut ℂ)) {a h : Matrix.GeneralLinearGroup (Fin n) ℂ}
    (ha : a ∈ g2l_GammaL H hH b L)
    (hh : h ∈ g1_zeroSet (g1_vanishingIdealSet (g2l_GammaL H hH b L₀) :
      Set (MvPolynomial (Fin n × Fin n) ℂ))) :
    a * h ∈ g1_zeroSet (g1_vanishingIdealSet (g2l_GammaL H hH b L₀) :
      Set (MvPolynomial (Fin n × Fin n) ℂ)) := by
  intro f hf
  have hf' : g1_leftTranslate a f ∈ g1_vanishingIdealSet (g2l_GammaL H hH b L₀) := by
    refine (g2l_mem_I₀_iff H hH b hL₀ _).mpr fun L' g hg => ?_
    rw [g1_eval_leftTranslate]
    exact (g2l_mem_I₀_iff H hH b hL₀ f).mp hf (L ++ L') _ (by
      rw [g2l_GammaL_append]; exact ⟨a, ha, g, hg, rfl⟩)
  have := hh _ hf'
  rwa [g1_eval_leftTranslate] at this

theorem g2l_Z_mul {g h : Matrix.GeneralLinearGroup (Fin n) ℂ}
    (hg : g ∈ g1_zeroSet (g1_vanishingIdealSet (g2l_GammaL H hH b L₀) :
      Set (MvPolynomial (Fin n × Fin n) ℂ)))
    (hh : h ∈ g1_zeroSet (g1_vanishingIdealSet (g2l_GammaL H hH b L₀) :
      Set (MvPolynomial (Fin n × Fin n) ℂ))) :
    g * h ∈ g1_zeroSet (g1_vanishingIdealSet (g2l_GammaL H hH b L₀) :
      Set (MvPolynomial (Fin n × Fin n) ℂ)) := by
  intro f hf
  have hf' : g2l_rightMulAlgHom h f ∈ g1_vanishingIdealSet (g2l_GammaL H hH b L₀) := by
    refine g1_mem_vanishingIdealSet_iff.mpr fun x hx => ?_
    rw [g2l_eval_rightMulAlgHom]
    exact g2l_Z_mul_left H hH b hL₀ L₀ hx hh f hf
  have := hg _ hf'
  rwa [g2l_eval_rightMulAlgHom] at this

/-- **Inverses.** The closure `Z` is closed under inverses: left translation by `g ∈ Z` maps the
prime `I(Z)` into itself, and the preimage of `I(Z)` under this automorphism is a prime of the
same finite dimension containing it, hence equal to it. -/
theorem g2l_Z_inv (m : ℕ)
    (hm : ringKrullDim (MvPolynomial (Fin n × Fin n) ℂ ⧸
      g1_vanishingIdealSet (g2l_GammaL H hH b L₀)) = m)
    {g : Matrix.GeneralLinearGroup (Fin n) ℂ}
    (hg : g ∈ g1_zeroSet (g1_vanishingIdealSet (g2l_GammaL H hH b L₀) :
      Set (MvPolynomial (Fin n × Fin n) ℂ))) :
    g⁻¹ ∈ g1_zeroSet (g1_vanishingIdealSet (g2l_GammaL H hH b L₀) :
      Set (MvPolynomial (Fin n × Fin n) ℂ)) := by
  set I₀ := g1_vanishingIdealSet (g2l_GammaL H hH b L₀)
  have hP : I₀.IsPrime := g2l_GammaL_isPrime H hH b L₀
  let φ := g1s_translate g
  have hφ : ∀ f ∈ I₀, φ f ∈ I₀ := by
    intro f hf
    refine g1_mem_vanishingIdealSet_iff.mpr fun x hx => ?_
    rw [g1s_eval_translate]
    exact g2l_Z_mul H hH b hL₀ hg (g2l_GammaL_subset_Z H hH b hL₀ L₀ hx) f hf
  set I₁ := I₀.comap φ.toRingHom
  have hle : I₀ ≤ I₁ := fun f hf => hφ f hf
  have hsurj : Function.Surjective φ := fun f =>
    ⟨g1s_translate g⁻¹ f, by
      change g1s_translate g (g1s_translate g⁻¹ f) = f
      rw [g1s_translate_translate, inv_mul_cancel, g1s_translate_one]⟩
  have hdim1 : ringKrullDim (MvPolynomial (Fin n × Fin n) ℂ ⧸ I₁) = m := by
    let ψ : MvPolynomial (Fin n × Fin n) ℂ →+* MvPolynomial (Fin n × Fin n) ℂ ⧸ I₀ :=
      (Ideal.Quotient.mk I₀).comp φ.toRingHom
    have hψ : Function.Surjective ψ := Ideal.Quotient.mk_surjective.comp hsurj
    have hker : RingHom.ker ψ = I₁ := by
      ext f
      simp only [RingHom.mem_ker, ψ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, I₁,
        Ideal.mem_comap]
    rw [← hker, ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hψ), hm]
  have heq : I₀ = I₁ := by
    by_contra hne
    exact g1_ringKrullDim_quotient_ne_of_lt I₀ I₁ (lt_of_le_of_ne hle hne) m hm hdim1
  intro f hf
  have hcomp : g1s_translate g (g1s_translate g⁻¹ f) = f := by
    rw [g1s_translate_translate, inv_mul_cancel, g1s_translate_one]
  have h0 : g1s_translate g⁻¹ f ∈ I₁ := by
    rw [Ideal.mem_comap]
    exact (congrArg (· ∈ I₀) hcomp).mpr hf
  have h1 : g1s_translate g⁻¹ f ∈ I₀ := heq.symm ▸ h0
  have h2 := g1_mem_vanishingIdealSet_iff.mp h1 1 (g2l_one_mem_GammaL H hH b L₀)
  rwa [g1s_eval_translate, mul_one] at h2

/-- The vanishing ideal of the stable product is `Aut(ℂ)`-stable. -/
theorem g2l_I₀_map (σ : RingAut ℂ) {f : MvPolynomial (Fin n × Fin n) ℂ}
    (hf : f ∈ g1_vanishingIdealSet (g2l_GammaL H hH b L₀)) :
    MvPolynomial.map (σ : ℂ →+* ℂ) f ∈ g1_vanishingIdealSet (g2l_GammaL H hH b L₀) := by
  refine (g2l_mem_I₀_iff H hH b hL₀ _).mpr fun L g hg => ?_
  have h := g2l_eval_map_symm σ.symm (g1_coords g) f
  rw [RingEquiv.symm_symm] at h
  rw [h]
  have hmem := g2l_map_mem_GammaL H hH b σ.symm L hg
  have := (g2l_mem_I₀_iff H hH b hL₀ f).mp hf _ _ hmem
  rw [g2l_coords_map] at this
  rw [this, map_zero]

/-- The closure of the stable product, as the zero set of rational polynomials. -/
theorem g2l_Z_eq_ratZeroSet :
    g1_zeroSet (g1_vanishingIdealSet (g2l_GammaL H hH b L₀) :
      Set (MvPolynomial (Fin n × Fin n) ℂ)) =
      g2_ratZeroSet {p | MvPolynomial.map (algebraMap ℚ ℂ) p ∈
        g1_vanishingIdealSet (g2l_GammaL H hH b L₀)} := by
  ext g
  constructor
  · intro hg p hp
    have := hg _ hp
    rwa [eval_map, ← aeval_def] at this
  · intro hg f hf
    have hdesc := g2l_mvPolynomial_descent
      ((g1_vanishingIdealSet (g2l_GammaL H hH b L₀)).restrictScalars ℂ)
      (fun σ f hf => g2l_I₀_map H hH b hL₀ σ hf) (f := f) hf
    let ev : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ := (aeval (g1_coords g)).toLinearMap
    have hle : Submodule.span ℂ {f' | f' ∈ (g1_vanishingIdealSet (g2l_GammaL H hH b L₀)).restrictScalars ℂ ∧
        ∃ p : MvPolynomial (Fin n × Fin n) ℚ, MvPolynomial.map (algebraMap ℚ ℂ) p = f'} ≤
        LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨hf', p, rfl⟩
      change eval (g1_coords g) (MvPolynomial.map (algebraMap ℚ ℂ) p) = 0
      rw [eval_map, ← aeval_def]
      exact hg p hf'
    exact hle hdesc

end Closure

section Main

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
  {n : ℕ} (b : Module.Basis (Fin n) ℚ V)

theorem g2l_circleImage_subset_GammaL :
    g2_circleImage H hH b ⊆ g2l_GammaL H hH b [RingEquiv.refl ℂ] := by
  rintro g ⟨z, hz⟩
  rw [g2l_GammaL_eq]
  refine ⟨g, ⟨Circle.toUnits z, ?_⟩, 1, by simp, mul_one g⟩
  ext a c
  rw [g2l_torusGL_val, hz, g2l_toMatrix_circleAction]
  congr 2

/-- The constructed Hodge group as a matrix algebraic group.
Source: Mumford, *Families of abelian varieties*, Proc. Sympos. Pure Math. 9 (1966), §1; Borel, *Linear Algebraic Groups*, 2nd ed., §1.1. -/
def g2l_hodgeAlg : MatrixAlgGroup ℂ n :=
  g1_ofEquations ((MvPolynomial.map (algebraMap ℚ ℂ)) '' g2l_hgEquations H hH b)
    (g2l_hodgeSubgroup H hH b) (by
      intro g
      change g ∈ g2_hodgeGroup H hH b ↔ _
      rw [g2l_hodgeGroup_eq_ratZeroSet]
      constructor
      · rintro hg _ ⟨p, hp, rfl⟩
        rw [eval_map, ← aeval_def]
        exact hg p hp
      · intro hg p hp
        have := hg _ ⟨p, hp, rfl⟩
        rwa [eval_map, ← aeval_def] at this)

example : @g2l_hodgeAlg = @g2l_hodgeAlg := rfl

/-- **The Krull dimension of the Hodge group is at most `dim 𝔥`.** -/
theorem g2l_ringKrullDim_hodgeGroup_le :
    ringKrullDim (MvPolynomial (Fin n × Fin n) ℂ ⧸ g1_vanishingIdealSet (g2_hodgeGroup H hH b)) ≤
      Module.finrank ℂ (g2l_hM H hH b) := by
  obtain ⟨L₀, hdim, hL₀⟩ := g2l_exists_GammaL_stable H hH b
  obtain ⟨m, hm, hmr⟩ := g2l_exists_nat_of_le (g2l_dim_GammaL_nonneg H hH b L₀) hdim
  set Z := g1_zeroSet (g1_vanishingIdealSet (g2l_GammaL H hH b L₀) :
    Set (MvPolynomial (Fin n × Fin n) ℂ))
  have hZalg : g2_IsRatAlgSubgroup Z := by
    refine ⟨⟨_, g2l_Z_eq_ratZeroSet H hH b hL₀⟩, ?_, fun x hx y hy => g2l_Z_mul H hH b hL₀ hx hy,
      fun x hx => g2l_Z_inv H hH b hL₀ m hm hx⟩
    exact g2l_GammaL_subset_Z H hH b hL₀ L₀ (g2l_one_mem_GammaL H hH b L₀)
  have hcirc : g2_circleImage H hH b ⊆ Z := fun g hg =>
    g2l_GammaL_subset_Z H hH b hL₀ _ (g2l_circleImage_subset_GammaL H hH b hg)
  have hHgZ : g2_hodgeGroup H hH b ⊆ Z := Set.sInter_subset_of_mem ⟨hZalg, hcirc⟩
  have hle : g1_vanishingIdealSet (g2l_GammaL H hH b L₀) ≤
      g1_vanishingIdealSet (g2_hodgeGroup H hH b) := fun f hf =>
    g1_mem_vanishingIdealSet_iff.mpr fun g hg => hHgZ hg f hf
  exact (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle)).trans hdim

/-- **The Lie algebra of the constructed Hodge group is the complexified Hodge Lie algebra.** -/
theorem g2l_lie_hodgeGroup :
    g1_lieOfSet (g2_hodgeGroup H hH b) =
      (complexSpan (hodgeLieAlgebra H hH).toSubmodule).map
        (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
          (Algebra.TensorProduct.basis ℂ b)).toLinearMap := by
  rw [g2l_map_complexSpan]
  have hsub := g2l_span_hodgeLie_le H hH b
  have hfin := g1_finrank_lie_eq_krullDim (g2l_hodgeAlg H hH b)
  have hdim := g2l_ringKrullDim_hodgeGroup_le H hH b
  change (Module.finrank ℂ (g1_lieOfSet (g2_hodgeGroup H hH b)) : WithBot ℕ∞) =
    ringKrullDim (MvPolynomial (Fin n × Fin n) ℂ ⧸
      g1_vanishingIdealSet (g2_hodgeGroup H hH b)) at hfin
  have hr : Module.finrank ℂ (g1_lieOfSet (g2_hodgeGroup H hH b)) ≤
      Module.finrank ℂ (g2l_hM H hH b) := by
    have := hfin.le.trans hdim
    exact_mod_cast this
  exact (Submodule.eq_of_le_of_finrank_le hsub hr).symm

end Main

end HodgeLean.Foundations
