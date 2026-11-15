import HodgeLean.Foundations.HodgeGroupAlgebraicTorus
import HodgeLean.Foundations.HodgeGroupAlgebraicJacobian

/-! # The dimension of a product of tori (Track G2, helper for the Lie bridge)

`g2l_ringKrullDim_Gamma_le`: if a subspace `W ⊆ 𝔤𝔩_n` contains the grading matrices of frames
`Q_1, …, Q_N` and is stable under the bracket with each of them, the Zariski closure of the set
of products `T_1 ⋯ T_N` of their tori has Krull dimension at most `dim W`. The product map is
parametrized by the hyperbola torus `g2l_hypGroup N ⊆ GL_{2N}`; its tangent vectors lie in left
translates of `W` (`g2l_Tame`, `g2l_conj_mem_spanS`), and the Jacobian bound of
`HodgeGroupAlgebraicJacobian` turns this into a bound on algebraically independent functions.
`g2l_vanishingIdealSet_Gamma_isPrime`: these products are irreducible.

Sources: Borel, *Linear Algebraic Groups*, 2nd ed., §2.2, §3.4, AG.10 and AG.15.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace HodgeLean.Foundations

open MvPolynomial HodgeLean.Foundations.Program
open scoped Pointwise

section DiagFrame

variable {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal frame of a map `κ` from the coordinates to a finite set: `Q i` projects onto
the coordinates `a` with `κ a = i`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.2 (the diagonal torus). -/
def g2l_diagFrame (κ : Fin m → ι) : ι → Matrix (Fin m) (Fin m) ℂ :=
  fun i => Matrix.diagonal fun a => if κ a = i then 1 else 0

example : @g2l_diagFrame = @g2l_diagFrame := rfl

theorem g2l_isFrame_diagFrame (κ : Fin m → ι) : g2l_IsFrame (g2l_diagFrame κ) := by
  refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
  · rw [g2l_diagFrame, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    split_ifs <;> simp
  · rw [g2l_diagFrame, g2l_diagFrame, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_zero]
    congr 1
    funext a
    split_ifs with h1 h2 <;> simp_all
  · ext a b
    rw [Matrix.sum_apply]
    simp only [g2l_diagFrame, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with hab
    · subst hab
      simp
    · simp

theorem g2l_torusAt_diagFrame (κ : Fin m → ι) (w : ι → ℤ) (τ : ℂˣ) :
    g2l_torusAt (g2l_diagFrame κ) w τ = Matrix.diagonal fun a => ((τ ^ w (κ a) : ℂˣ) : ℂ) := by
  ext a b
  rw [g2l_torusAt, Matrix.sum_apply]
  simp only [g2l_diagFrame, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with hab
  · subst hab
    simp
  · simp

theorem g2l_frameD_diagFrame (κ : Fin m → ι) (w : ι → ℤ) :
    g2l_frameD (g2l_diagFrame κ) w = Matrix.diagonal fun a => (w (κ a) : ℂ) := by
  ext a b
  rw [g2l_frameD, Matrix.sum_apply]
  simp only [g2l_diagFrame, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with hab
  · subst hab
    simp
  · simp

end DiagFrame

section Hyperbola

variable {N : ℕ}

/-- The diagonal matrix `diag(t_1, …, t_N, t_1⁻¹, …, t_N⁻¹)`, as an element of `GL_{2N}(ℂ)`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.2 and §8.5 (the torus `G_m^N`). -/
def g2l_hypGL : (Fin N → ℂˣ) →* Matrix.GeneralLinearGroup (Fin (N + N)) ℂ where
  toFun t := ⟨Matrix.diagonal (Fin.append (fun l => (t l : ℂ)) (fun l => ((t l)⁻¹ : ℂˣ))),
    Matrix.diagonal (Fin.append (fun l => ((t l)⁻¹ : ℂˣ)) (fun l => (t l : ℂ))),
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      refine Fin.addCases (fun l => ?_) (fun l => ?_) a <;>
        simp only [Fin.append_left, Fin.append_right] <;> simp,
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      refine Fin.addCases (fun l => ?_) (fun l => ?_) a <;>
        simp only [Fin.append_left, Fin.append_right] <;> simp⟩
  map_one' := by
    ext a b
    simp only [Pi.one_apply, Units.val_one, inv_one]
    rw [show (Fin.append (fun _ : Fin N => (1 : ℂ)) fun _ => 1) = fun _ => 1 by
      funext a; refine Fin.addCases (fun l => ?_) (fun l => ?_) a <;>
        simp only [Fin.append_left, Fin.append_right]]
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  map_mul' s t := by
    ext a b
    simp only [Pi.mul_apply, Units.val_mul, mul_inv_rev]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    refine Fin.addCases (fun l => ?_) (fun l => ?_) a <;>
      simp only [Fin.append_left, Fin.append_right]
    · simp [mul_comm]

example : @g2l_hypGL = @g2l_hypGL := rfl

theorem g2l_hypGL_val (t : Fin N → ℂˣ) :
    ((g2l_hypGL t : Matrix.GeneralLinearGroup (Fin (N + N)) ℂ) : Matrix (Fin (N + N))
      (Fin (N + N)) ℂ) = Matrix.diagonal (Fin.append (fun l => (t l : ℂ))
        (fun l => ((t l)⁻¹ : ℂˣ))) := rfl

/-- The equations of the hyperbola torus: the off-diagonal entries and `x_{l,l} x_{N+l,N+l} - 1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6 and §8.2. -/
def g2l_hypEquations : Set (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ) :=
  {f | ∃ a b, a ≠ b ∧ f = X (a, b)} ∪
    {f | ∃ l : Fin N, f = X (Fin.castAdd N l, Fin.castAdd N l) *
      X (Fin.natAdd N l, Fin.natAdd N l) - 1}

example : @g2l_hypEquations = @g2l_hypEquations := rfl

theorem g2l_mem_hyp_iff (g : Matrix.GeneralLinearGroup (Fin (N + N)) ℂ) :
    g ∈ (g2l_hypGL (N := N)).range ↔
      ∀ f ∈ g2l_hypEquations, eval (g1_coords g) f = 0 := by
  constructor
  · rintro ⟨t, rfl⟩ f (⟨a, b, hab, rfl⟩ | ⟨l, rfl⟩)
    · simp [g1_coords, g2l_hypGL_val, hab]
    · simp only [g1_coords, g2l_hypGL_val, map_sub, map_mul, eval_X, map_one,
        Matrix.diagonal_apply_eq, Fin.append_left, Fin.append_right]
      simp
  · intro h
    have hoff : ∀ a b, a ≠ b → (g : Matrix _ _ ℂ) a b = 0 := fun a b hab => by
      simpa [g1_coords] using h _ (Or.inl ⟨a, b, hab, rfl⟩)
    have hdiag : ∀ l : Fin N, (g : Matrix _ _ ℂ) (Fin.castAdd N l) (Fin.castAdd N l) *
        (g : Matrix _ _ ℂ) (Fin.natAdd N l) (Fin.natAdd N l) = 1 := fun l => by
      have := h _ (Or.inr ⟨l, rfl⟩)
      simpa [g1_coords, sub_eq_zero] using this
    let t : Fin N → ℂˣ := fun l => ⟨(g : Matrix _ _ ℂ) (Fin.castAdd N l) (Fin.castAdd N l),
      (g : Matrix _ _ ℂ) (Fin.natAdd N l) (Fin.natAdd N l), hdiag l,
      by rw [mul_comm]; exact hdiag l⟩
    refine ⟨t, Units.ext ?_⟩
    ext a b
    rw [g2l_hypGL_val, Matrix.diagonal_apply]
    split_ifs with hab
    · subst hab
      refine Fin.addCases (fun l => ?_) (fun l => ?_) a
      · simp [t]
      · simp only [Fin.append_right]
        rw [Units.val_inv_eq_inv_val]
        change (t l : ℂ)⁻¹ = _
        rw [inv_eq_of_mul_eq_one_right (hdiag l)]
    · exact (hoff a b hab).symm

/-- The hyperbola torus `{diag(t, t⁻¹)}` as a matrix algebraic group in `GL_{2N}`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.2. -/
def g2l_hypGroup (N : ℕ) : MatrixAlgGroup ℂ (N + N) :=
  g1_ofEquations g2l_hypEquations g2l_hypGL.range g2l_mem_hyp_iff

example : @g2l_hypGroup = @g2l_hypGroup := rfl

/-- The coordinate partition singling out `l` and `N + l`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.2 (coordinates of the diagonal torus). -/
def g2l_hypKappa (l : Fin N) (a : Fin (N + N)) : Fin 3 :=
  if a = Fin.castAdd N l then 0 else if a = Fin.natAdd N l then 1 else 2

example : @g2l_hypKappa = @g2l_hypKappa := rfl

/-- The weights `1, -1, 0`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.5 (the cocharacter `t ↦ diag(t, t⁻¹)`). -/
def g2l_hypW : Fin 3 → ℤ := ![1, -1, 0]

example : @g2l_hypW = @g2l_hypW := rfl

/-- The tangent direction `E_{l,l} - E_{N+l,N+l}` of the hyperbola torus.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.6 (the Lie algebra of a torus). -/
def g2l_hypZ (l : Fin N) : Matrix (Fin (N + N)) (Fin (N + N)) ℂ :=
  g2l_frameD (g2l_diagFrame (g2l_hypKappa l)) g2l_hypW

example : @g2l_hypZ = @g2l_hypZ := rfl

theorem g2l_castAdd_ne_natAdd (l l' : Fin N) : Fin.castAdd N l ≠ Fin.natAdd N l' := by
  intro e
  have := congrArg Fin.val e
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem g2l_hypKappa_castAdd (l l' : Fin N) :
    g2l_hypKappa l (Fin.castAdd N l') = if l' = l then 0 else 2 := by
  unfold g2l_hypKappa
  rw [ite_eq_right (g2l_castAdd_ne_natAdd l' l)]
  by_cases h : l' = l
  · subst h; simp
  · rw [ite_eq_right (fun e => h (Fin.castAdd_inj.mp e)), ite_eq_right h]

theorem g2l_hypKappa_natAdd (l l' : Fin N) :
    g2l_hypKappa l (Fin.natAdd N l') = if l' = l then 1 else 2 := by
  unfold g2l_hypKappa
  rw [ite_eq_right (fun e => g2l_castAdd_ne_natAdd l l' e.symm)]
  by_cases h : l' = l
  · subst h; simp
  · rw [ite_eq_right (fun e => h (Fin.ext (by
      have := congrArg Fin.val e; simp only [Fin.val_natAdd] at this; omega))), ite_eq_right h]

theorem g2l_torusGL_hypKappa (l : Fin N) (τ : ℂˣ) :
    g2l_torusGL (g2l_isFrame_diagFrame (g2l_hypKappa l)) g2l_hypW τ =
      g2l_hypGL (Pi.mulSingle l τ) := by
  ext a b
  rw [g2l_torusGL_val, g2l_torusAt_diagFrame, g2l_hypGL_val]
  simp only [Matrix.diagonal_apply]
  split_ifs with hab
  · subst hab
    refine Fin.addCases (fun l' => ?_) (fun l' => ?_) a
    · rw [g2l_hypKappa_castAdd, Fin.append_left]
      by_cases h : l' = l
      · subst h; simp [g2l_hypW]
      · simp [g2l_hypW, h, Pi.mulSingle_apply]
    · rw [g2l_hypKappa_natAdd, Fin.append_right]
      by_cases h : l' = l
      · subst h; simp [g2l_hypW]
      · simp [g2l_hypW, h, Pi.mulSingle_apply]
  · rfl

theorem g2l_hypZ_mem (l : Fin N) : g2l_hypZ l ∈ g1_lieAlgebra (g2l_hypGroup N) :=
  g2l_frameD_mem_lieOfSet (g2l_isFrame_diagFrame _) g2l_hypW fun τ => by
    rw [g2l_torusGL_hypKappa]
    exact ⟨_, rfl⟩

theorem g2l_hypZ_apply (l : Fin N) (a b : Fin (N + N)) :
    g2l_hypZ l a b = if a = b then (g2l_hypW (g2l_hypKappa l a) : ℂ) else 0 := by
  rw [g2l_hypZ, g2l_frameD_diagFrame, Matrix.diagonal_apply]

theorem g2l_lie_hyp_le :
    g1_lieAlgebra (g2l_hypGroup N) ≤ Submodule.span ℂ (Set.range (g2l_hypZ (N := N))) := by
  intro Y hY
  have hmem : ∀ f ∈ g2l_hypEquations (N := N), g1_differential f Y = 0 := fun f hf =>
    g1_mem_lieOfSet_iff.mp hY f
      (g1_equations_le_vanishingIdeal (g2l_hypGroup N) (Ideal.subset_span hf))
  have hoff : ∀ a b, a ≠ b → Y a b = 0 := fun a b hab => by
    have := hmem _ (Or.inl ⟨a, b, hab, rfl⟩)
    rwa [g1_differential_X] at this
  have hdiag : ∀ l : Fin N, Y (Fin.natAdd N l) (Fin.natAdd N l) =
      -Y (Fin.castAdd N l) (Fin.castAdd N l) := fun l => by
    have := hmem _ (Or.inr ⟨l, rfl⟩)
    have h2 : g1_differential (X (Fin.castAdd N l, Fin.castAdd N l) *
        X (Fin.natAdd N l, Fin.natAdd N l) - 1 : MvPolynomial _ ℂ) Y =
        g1_differential (X (Fin.castAdd N l, Fin.castAdd N l) *
          X (Fin.natAdd N l, Fin.natAdd N l) : MvPolynomial _ ℂ) Y -
        g1_differential (1 : MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ) Y := by
      change g1s_diffLin ℂ (N + N) _ Y = g1s_diffLin ℂ (N + N) _ Y - g1s_diffLin ℂ (N + N) _ Y
      rw [map_sub]
      rfl
    rw [h2, g1_differential_mul, g1_differential_X, g1_differential_X,
      show (1 : MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ) = C 1 from rfl,
      g1_differential_C] at this
    simp only [eval_X, g1_coords, Units.val_one, Matrix.one_apply_eq, one_mul, sub_zero] at this
    linear_combination this
  have hY : Y = ∑ l, Y (Fin.castAdd N l) (Fin.castAdd N l) • g2l_hypZ l := by
    ext a b
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, g2l_hypZ_apply]
    by_cases hab : a = b
    · subst hab
      simp only [ite_true]
      refine Fin.addCases (fun l' => ?_) (fun l' => ?_) a
      · simp only [g2l_hypKappa_castAdd]
        rw [Finset.sum_eq_single l']
        · simp [g2l_hypW]
        · intro l _ hl; simp [g2l_hypW, Ne.symm hl]
        · simp
      · simp only [g2l_hypKappa_natAdd]
        rw [Finset.sum_eq_single l', hdiag]
        · simp [g2l_hypW]
        · intro l _ hl; simp [g2l_hypW, Ne.symm hl]
        · simp
    · simp [hab, hoff a b hab]
  rw [hY]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem g2l_finrank_lie_hyp_le : Module.finrank ℂ (g1_lieAlgebra (g2l_hypGroup N)) ≤ N :=
  (Submodule.finrank_mono g2l_lie_hyp_le).trans ((finrank_range_le_card _).trans (by simp))

theorem g2l_ringKrullDim_hyp_le :
    ringKrullDim (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸
      g1_vanishingIdeal (g2l_hypGroup N)) ≤ N :=
  (g1s_ringKrullDim_le_finrank _).trans (by exact_mod_cast g2l_finrank_lie_hyp_le)

end Hyperbola

section SpanS

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : Type*) [CommRing S] [Algebra ℂ S]

/-- The `S`-span `W ⊗ S` of a complex subspace `W` of matrices, inside matrices over `S`.
Source: Bourbaki, *Algèbre*, ch. II, §5 (extension of scalars). -/
def g2l_spanS (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) : Submodule S (Matrix (Fin n) (Fin n) S) :=
  Submodule.span S ((fun Z : Matrix (Fin n) (Fin n) ℂ => Z.map (algebraMap ℂ S)) '' W)

example : @g2l_spanS = @g2l_spanS := rfl

variable {S}

theorem g2l_map_mem_spanS {W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)}
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z ∈ W) : Z.map (algebraMap ℂ S) ∈ g2l_spanS S W :=
  Submodule.subset_span ⟨Z, hZ, rfl⟩

/-- **Torus conjugation preserves `W ⊗ S`**, when `W` is stable under the bracket with the
grading matrix of the frame. -/
theorem g2l_conj_mem_spanS {Q : ι → Matrix (Fin n) (Fin n) ℂ} (hQ : g2l_IsFrame Q) (w : ι → ℤ)
    (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hW : ∀ Y ∈ W, g2l_frameD Q w * Y - Y * g2l_frameD Q w ∈ W) (τ : Sˣ)
    {Y : Matrix (Fin n) (Fin n) S} (hY : Y ∈ g2l_spanS S W) :
    g2l_torusAt (fun i => (Q i).map (algebraMap ℂ S)) w τ⁻¹ * Y *
      g2l_torusAt (fun i => (Q i).map (algebraMap ℂ S)) w τ ∈ g2l_spanS S W := by
  classical
  have hQS : g2l_IsFrame (fun i => (Q i).map (algebraMap ℂ S)) := hQ.map _
  induction hY using Submodule.span_induction with
  | mem Y hY =>
    obtain ⟨Z, hZ, rfl⟩ := hY
    rw [g2l_torusAt_conj w hQS]
    have hblock : ∀ p : ι × ι, (Q p.1).map (algebraMap ℂ S) * Z.map (algebraMap ℂ S) *
        (Q p.2).map (algebraMap ℂ S) = (Q p.1 * Z * Q p.2).map (algebraMap ℂ S) := fun p => by
      rw [Matrix.map_mul, Matrix.map_mul]
    simp only [hblock]
    set K : Finset ℤ := Finset.univ.image (fun p : ι × ι => w p.2 - w p.1)
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := K)
      (g := fun p : ι × ι => w p.2 - w p.1) (fun p _ => Finset.mem_image_of_mem _ (by simp))]
    refine Submodule.sum_mem _ fun k _ => ?_
    have : ∑ p ∈ Finset.univ.filter (fun p : ι × ι => w p.2 - w p.1 = k),
        ((τ ^ (w p.2 - w p.1) : Sˣ) : S) • (Q p.1 * Z * Q p.2).map (algebraMap ℂ S) =
        ((τ ^ k : Sˣ) : S) • (g2l_weightComp Q w k Z).map (algebraMap ℂ S) := by
      rw [g2l_weightComp]
      have h := map_sum (algebraMap ℂ S).mapMatrix (fun p : ι × ι => Q p.1 * Z * Q p.2)
        (Finset.univ.filter (fun p : ι × ι => w p.2 - w p.1 = k))
      simp only [RingHom.mapMatrix_apply] at h
      rw [h, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.mp hp).2]
    rw [this]
    exact Submodule.smul_mem _ _ (g2l_map_mem_spanS (g2l_weightComp_mem hQ w W hW hZ k))
  | zero => simp
  | add x y _ _ hx hy => simpa [Matrix.mul_add, Matrix.add_mul] using add_mem hx hy
  | smul a x _ hx => simpa [Matrix.mul_smul, Matrix.smul_mul] using Submodule.smul_mem _ a hx

end SpanS

section Deriv

variable {n : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R]

/-- The Leibniz rule for a derivation applied entrywise to a product of matrices. -/
theorem g2l_derivation_matrix_mul (D : Derivation ℂ R R) (A B : Matrix (Fin n) (Fin n) R) :
    (A * B).map D = A.map D * B + A * B.map D := by
  ext a b
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, Derivation.leibniz,
    smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  all_goals refine Finset.sum_congr rfl fun c _ => by ring

theorem g2l_derivation_matrix_one (D : Derivation ℂ R R) :
    (1 : Matrix (Fin n) (Fin n) R).map D = 0 := by
  ext a b
  by_cases h : a = b
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

variable {S : Type*} [CommRing S] [Algebra ℂ S]

/-- A matrix `A` over `R` whose image in `S` is the invertible `g`, with `g⁻¹ (D A)‾` in `W ⊗ S`
and conjugation by `g` preserving `W ⊗ S`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.4 (left-invariant derivations) and §7.5 (products of subvarieties through `1`). -/
def g2l_Tame (φ : R →+* S) (D : Derivation ℂ R R) (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (A : Matrix (Fin n) (Fin n) R) (g : Matrix.GeneralLinearGroup (Fin n) S) : Prop :=
  A.map φ = g ∧ ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) S) : Matrix (Fin n) (Fin n) S) *
      ((A.map D).map φ) ∈ g2l_spanS S W ∧
    ∀ Y ∈ g2l_spanS S W,
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) S) : Matrix (Fin n) (Fin n) S) * Y * g ∈
        g2l_spanS S W

example : @g2l_Tame = @g2l_Tame := rfl

theorem g2l_tame_one (φ : R →+* S) (D : Derivation ℂ R R)
    (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) : g2l_Tame φ D W 1 1 := by
  refine ⟨?_, ?_, fun Y hY => ?_⟩
  · rw [Matrix.map_one _ (map_zero φ) (map_one φ)]; rfl
  · rw [g2l_derivation_matrix_one, Matrix.map_zero _ (map_zero φ), Matrix.mul_zero]
    exact Submodule.zero_mem _
  · simpa using hY

theorem g2l_tame_mul (φ : R →+* S) (D : Derivation ℂ R R)
    (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) {A B : Matrix (Fin n) (Fin n) R}
    {g h : Matrix.GeneralLinearGroup (Fin n) S} (hA : g2l_Tame φ D W A g)
    (hB : g2l_Tame φ D W B h) : g2l_Tame φ D W (A * B) (g * h) := by
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  refine ⟨?_, ?_, fun Y hY => ?_⟩
  · rw [Matrix.map_mul, hA1, hB1]; rfl
  · rw [g2l_derivation_matrix_mul, Matrix.map_add _ (map_add φ), Matrix.map_mul,
      Matrix.map_mul, hA1, hB1, mul_inv_rev, Matrix.mul_add]
    refine add_mem ?_ ?_
    · have := hB3 _ hA2
      convert this using 1
      simp only [Units.val_mul, Matrix.mul_assoc]
    · convert hB2 using 1
      simp only [Units.val_mul, Matrix.mul_assoc]
      congr 1
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  · have := hB3 _ (hA3 Y hY)
    convert this using 1
    simp only [mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem g2l_tame_prod (φ : R →+* S) (D : Derivation ℂ R R)
    (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) {N : ℕ} (A : Fin N → Matrix (Fin n) (Fin n) R)
    (g : Fin N → Matrix.GeneralLinearGroup (Fin n) S) (h : ∀ l, g2l_Tame φ D W (A l) (g l)) :
    g2l_Tame φ D W (List.ofFn A).prod (List.ofFn g).prod := by
  induction N with
  | zero => simpa using g2l_tame_one φ D W
  | succ N ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact g2l_tame_mul φ D W (h 0) (ih _ _ fun l => h l.succ)

end Deriv

section TorusUnit

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A]

/-- The torus of a frame over a commutative ring, as a homomorphism `Aˣ → GL_n(A)`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.5. -/
def g2l_torusUnit {Q : ι → Matrix (Fin n) (Fin n) A} (hQ : g2l_IsFrame Q) (w : ι → ℤ) :
    Aˣ →* Matrix.GeneralLinearGroup (Fin n) A where
  toFun t := ⟨g2l_torusAt Q w t, g2l_torusAt Q w t⁻¹,
    by rw [g2l_torusAt_mul w hQ, mul_inv_cancel, g2l_torusAt_one w hQ],
    by rw [g2l_torusAt_mul w hQ, inv_mul_cancel, g2l_torusAt_one w hQ]⟩
  map_one' := Units.ext (g2l_torusAt_one w hQ)
  map_mul' s t := Units.ext (g2l_torusAt_mul w hQ s t).symm

example : @g2l_torusUnit = @g2l_torusUnit := rfl

theorem g2l_torusUnit_val {Q : ι → Matrix (Fin n) (Fin n) A} (hQ : g2l_IsFrame Q) (w : ι → ℤ)
    (t : Aˣ) : ((g2l_torusUnit hQ w t : Matrix.GeneralLinearGroup (Fin n) A) :
      Matrix (Fin n) (Fin n) A) = g2l_torusAt Q w t := rfl

theorem g2l_torusUnit_inv_val {Q : ι → Matrix (Fin n) (Fin n) A} (hQ : g2l_IsFrame Q)
    (w : ι → ℤ) (t : Aˣ) : (((g2l_torusUnit hQ w t)⁻¹ : Matrix.GeneralLinearGroup (Fin n) A) :
      Matrix (Fin n) (Fin n) A) = g2l_torusAt Q w t⁻¹ := by
  rw [← map_inv]; rfl

end TorusUnit

section Mu

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
  (Qs : Fin N → ι → Matrix (Fin n) (Fin n) ℂ) (w : ι → ℤ)

/-- The factor `l` of the product of tori, as a matrix over the coordinate ring of `GL_{2N}`,
in the variables `t_l = x_{l,l}` and `t_l⁻¹ = x_{N+l,N+l}`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §2.2 (the product morphism `T_1 × ⋯ × T_N → G`). -/
def g2l_psiR (l : Fin N) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ) :=
  g2l_psi (fun i => (Qs l i).map C) w (X (Fin.castAdd N l, Fin.castAdd N l))
    (X (Fin.natAdd N l, Fin.natAdd N l))

example : @g2l_psiR = @g2l_psiR := rfl

/-- The product `ψ_1 ⋯ ψ_N` of the factors.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §2.2. -/
def g2l_muR : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ) :=
  (List.ofFn (g2l_psiR Qs w)).prod

example : @g2l_muR = @g2l_muR := rfl

/-- Pulling back a polynomial along the product of tori.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §2.2 and AG.1.4 (comorphisms). -/
def g2l_muStar :
    MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ :=
  aeval fun ab => g2l_muR Qs w ab.1 ab.2

example : @g2l_muStar = @g2l_muStar := rfl

variable {Qs}

/-- The product of the tori of the frames `Qs l` at `t`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §2.2. -/
def g2l_prodTorus (hQs : ∀ l, g2l_IsFrame (Qs l)) (t : Fin N → ℂˣ) :
    Matrix.GeneralLinearGroup (Fin n) ℂ :=
  (List.ofFn fun l => g2l_torusGL (hQs l) w (t l)).prod

example : @g2l_prodTorus = @g2l_prodTorus := rfl

/-- The set of products of the tori of the frames `Qs l`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §2.2 (the group generated by irreducible subvarieties through `1`). -/
def g2l_Gamma (hQs : ∀ l, g2l_IsFrame (Qs l)) : Set (Matrix.GeneralLinearGroup (Fin n) ℂ) :=
  Set.range (g2l_prodTorus w hQs)

example : @g2l_Gamma = @g2l_Gamma := rfl

theorem g2l_eval_hyp_psiR (t : Fin N → ℂˣ) (l : Fin N) :
    (g2l_psiR Qs w l).map (eval (g1_coords (g2l_hypGL t))) = g2l_torusAt (Qs l) w (t l) := by
  rw [g2l_psiR, g2l_psi_map]
  have h1 : eval (g1_coords (g2l_hypGL t)) (X (Fin.castAdd N l, Fin.castAdd N l)) = (t l : ℂ) := by
    simp [g1_coords, g2l_hypGL_val]
  have h2 : eval (g1_coords (g2l_hypGL t)) (X (Fin.natAdd N l, Fin.natAdd N l)) =
      (((t l)⁻¹ : ℂˣ) : ℂ) := by
    simp only [eval_X, g1_coords, g2l_hypGL_val, Matrix.diagonal_apply_eq, Fin.append_right]
  rw [h1, h2, ← g2l_psi_units]
  congr 1
  funext i
  ext a b
  simp

theorem g2l_eval_hyp_muStar (hQs : ∀ l, g2l_IsFrame (Qs l)) (t : Fin N → ℂˣ)
    (f : MvPolynomial (Fin n × Fin n) ℂ) :
    eval (g1_coords (g2l_hypGL t)) (g2l_muStar Qs w f) =
      eval (g1_coords (g2l_prodTorus w hQs t)) f := by
  have hM : (g2l_muR Qs w).map (eval (g1_coords (g2l_hypGL t))) =
      ((g2l_prodTorus w hQs t : Matrix.GeneralLinearGroup (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ) := by
    have := map_list_prod (eval (g1_coords (g2l_hypGL (N := N) t))).mapMatrix
      (List.ofFn (g2l_psiR Qs w))
    simp only [RingHom.mapMatrix_apply, List.map_ofFn] at this
    rw [g2l_muR, this, g2l_prodTorus, ← Units.coeHom_apply, map_list_prod, List.map_ofFn]
    congr 1
    congr 1
    funext l
    simp only [Function.comp_apply, Units.coeHom_apply, g2l_torusGL_val]
    exact g2l_eval_hyp_psiR w t l
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ab hp =>
    simp only [map_mul, hp, g2l_muStar, aeval_X, eval_X]
    congr 1
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M ab.1 ab.2) hM
    simpa [g1_coords] using this

theorem g2l_mem_vanishingIdeal_Gamma_iff (hQs : ∀ l, g2l_IsFrame (Qs l))
    (f : MvPolynomial (Fin n × Fin n) ℂ) :
    f ∈ g1_vanishingIdealSet (g2l_Gamma w hQs) ↔
      g2l_muStar Qs w f ∈ g1_vanishingIdeal (g2l_hypGroup N) := by
  rw [g1_mem_vanishingIdealSet_iff]
  change _ ↔ g2l_muStar Qs w f ∈ g1_vanishingIdealSet (g2l_hypGL (N := N)).range
  rw [g1_mem_vanishingIdealSet_iff]
  constructor
  · rintro h _ ⟨t, rfl⟩
    rw [g2l_eval_hyp_muStar w hQs]
    exact h _ ⟨t, rfl⟩
  · rintro h _ ⟨t, rfl⟩
    rw [← g2l_eval_hyp_muStar w hQs]
    exact h _ ⟨t, rfl⟩

end Mu

/-- A finitely generated domain finite and injective over `ℂ[X_1, …, X_d]` has Krull dimension
`d`. -/
theorem g2l_ringKrullDim_eq_of_finite_inj {B : Type} [CommRing B] [IsDomain B] [Algebra ℂ B]
    {d : ℕ} (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] B) (hg : Function.Injective g)
    (hfinite : g.Finite) : ringKrullDim B = d := by
  let : Algebra (MvPolynomial (Fin d) ℂ) B := g.toAlgebra
  have : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) B :=
    IsScalarTower.of_algebraMap_eq (fun c ↦ (g.commutes c).symm)
  have : FaithfulSMul (MvPolynomial (Fin d) ℂ) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) B := ⟨hfinite.to_isIntegral⟩
  rw [PolynomialCatenary.ringKrullDim_eq_of_isIntegral_of_injective hg,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  simp

section Dim

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
  {Qs : Fin N → ι → Matrix (Fin n) (Fin n) ℂ} (w : ι → ℤ)

/-- The left-invariant derivation of `E_{l,l} - E_{N+l,N+l}` on `t_l = x_{l,l}`. -/
theorem g2l_leftDeriv_hypZ_t (j l : Fin N) :
    g1_leftDeriv (g2l_hypZ j) (X (Fin.castAdd N l, Fin.castAdd N l) :
      MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ) =
      (if l = j then 1 else 0) * X (Fin.castAdd N l, Fin.castAdd N l) := by
  rw [g1_leftDeriv, mkDerivation_X, Finset.sum_eq_single (Fin.castAdd N l)]
  · rw [g2l_hypZ_apply, ite_eq_left rfl, g2l_hypKappa_castAdd]
    by_cases h : l = j
    · subst h; simp [g2l_hypW, mul_comm]
    · simp [g2l_hypW, h]
  · intro b _ hb
    rw [g2l_hypZ_apply, ite_eq_right hb, C_0, mul_zero]
  · simp

theorem g2l_leftDeriv_hypZ_u (j l : Fin N) :
    g1_leftDeriv (g2l_hypZ j) (X (Fin.natAdd N l, Fin.natAdd N l) :
      MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ) =
      -((if l = j then 1 else 0) * X (Fin.natAdd N l, Fin.natAdd N l)) := by
  rw [g1_leftDeriv, mkDerivation_X, Finset.sum_eq_single (Fin.natAdd N l)]
  · rw [g2l_hypZ_apply, ite_eq_left rfl, g2l_hypKappa_natAdd]
    by_cases h : l = j
    · subst h; simp [g2l_hypW, mul_comm]
    · simp [g2l_hypW, h]
  · intro b _ hb
    rw [g2l_hypZ_apply, ite_eq_right hb, C_0, mul_zero]
  · simp

theorem g2l_hyp_eq_mem (l : Fin N) :
    (X (Fin.castAdd N l, Fin.castAdd N l) * X (Fin.natAdd N l, Fin.natAdd N l) - 1 :
      MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ) ∈ g1_vanishingIdeal (g2l_hypGroup N) :=
  g1_equations_le_vanishingIdeal _ (Ideal.subset_span (Or.inr ⟨l, rfl⟩))

/-- A polynomial identity for left-invariant derivations: `D_Y f = Σ (x Y)_{ab} ∂f/∂x_{ab}`. -/
theorem g2l_leftDeriv_eq_sum {k : Type*} [Field k] {m : ℕ} (Y : Matrix (Fin m) (Fin m) k)
    (f : MvPolynomial (Fin m × Fin m) k) :
    g1_leftDeriv Y f = ∑ ab : Fin m × Fin m,
      pderiv ab f * ∑ l, X (ab.1, l) * C (Y l ab.2) := by
  have := g1s_derivation_aeval (g1_leftDeriv Y) (fun ab => (X ab : MvPolynomial _ k)) f
  rw [aeval_X_left_apply] at this
  rw [this]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [aeval_X_left_apply, g1_leftDeriv, mkDerivation_X]

/-- **Dimension of a product of tori.** If a subspace `W ⊆ 𝔤𝔩_n` contains the grading matrices
of the frames `Qs l` and is stable under the bracket with each of them, the closure of the set
of products `T_1 ⋯ T_N` of their tori has dimension at most `dim W` (when its vanishing ideal is
prime). The tangent vectors of the product map lie in left translates of `W`, and the
characteristic-zero Jacobian bound turns this into a bound on algebraically independent
functions. -/
theorem g2l_ringKrullDim_Gamma_le (hQs : ∀ l, g2l_IsFrame (Qs l))
    (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (hD : ∀ l, g2l_frameD (Qs l) w ∈ W)
    (hW : ∀ l, ∀ Y ∈ W, g2l_frameD (Qs l) w * Y - Y * g2l_frameD (Qs l) w ∈ W)
    (hprime : (g1_vanishingIdealSet (g2l_Gamma w hQs)).IsPrime) :
    ringKrullDim (MvPolynomial (Fin n × Fin n) ℂ ⧸ g1_vanishingIdealSet (g2l_Gamma w hQs)) ≤
      Module.finrank ℂ W := by
  classical
  set I := g1_vanishingIdealSet (g2l_Gamma w hQs)
  set IX := g1_vanishingIdeal (g2l_hypGroup N)
  set μ := g2l_muStar Qs w
  have hIμ : I = IX.comap μ.toRingHom := by
    ext f
    rw [Ideal.mem_comap]
    exact g2l_mem_vanishingIdeal_Gamma_iff w hQs f
  -- a minimal prime `P` of `I(X)` with `μ⁻¹ P = I`
  have hrad : IX.IsRadical := g1s_vanishingIdeal_isRadical (g2l_hypGroup N)
  have hfin := IX.finite_minimalPrimes_of_isNoetherianRing
  obtain ⟨P, hPmin, hPI⟩ : ∃ P ∈ IX.minimalPrimes, P.comap μ.toRingHom = I := by
    have hinf : (hfin.toFinset.inf fun P => P.comap μ.toRingHom) ≤ I := by
      rw [hIμ]
      intro f hf
      rw [Ideal.mem_comap, ← hrad.radical, ← Ideal.sInf_minimalPrimes]
      refine Submodule.mem_sInf.mpr fun P hP => ?_
      have := (Finset.inf_le (f := fun P => P.comap μ.toRingHom)
        (hfin.mem_toFinset.mpr hP)) hf
      exact this
    obtain ⟨P, hP, hle⟩ := hprime.inf_le'.mp hinf
    refine ⟨P, hfin.mem_toFinset.mp hP, le_antisymm hle ?_⟩
    rw [hIμ]
    exact Ideal.comap_mono (hfin.mem_toFinset.mp hP).1.2
  have hPp : P.IsPrime := hPmin.1.1
  have hIXP : IX ≤ P := hPmin.1.2
  -- the quotient ring `S = R ⧸ P` and the units `t_l`
  let φ : MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ →+* _ ⧸ P := Ideal.Quotient.mk P
  have htu : ∀ l : Fin N, φ (X (Fin.castAdd N l, Fin.castAdd N l)) *
      φ (X (Fin.natAdd N l, Fin.natAdd N l)) = 1 := fun l => by
    rw [← map_mul, ← sub_eq_zero, ← map_one φ, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hIXP (g2l_hyp_eq_mem l)
  let τ : Fin N → (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P)ˣ := fun l =>
    ⟨φ (X (Fin.castAdd N l, Fin.castAdd N l)), φ (X (Fin.natAdd N l, Fin.natAdd N l)), htu l,
      by rw [mul_comm]; exact htu l⟩
  let QS : Fin N → ι → Matrix (Fin n) (Fin n) (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P) :=
    fun l i => (Qs l i).map (algebraMap ℂ _)
  have hQS : ∀ l, g2l_IsFrame (QS l) := fun l => (hQs l).map _
  let gl : Fin N → Matrix.GeneralLinearGroup (Fin n)
      (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P) := fun l => g2l_torusUnit (hQS l) w (τ l)
  have hφC : ∀ c : ℂ, φ (C c) = algebraMap ℂ _ c := fun c => rfl
  have hmapC : ∀ (Z : Matrix (Fin n) (Fin n) ℂ),
      (Z.map (C : ℂ →+* MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ)).map φ =
        Z.map (algebraMap ℂ _) := fun Z => by
    rw [Matrix.map_map]; rfl
  -- each factor is tame
  have hval : ∀ l, (g2l_psiR Qs w l).map φ = g2l_torusAt (QS l) w (τ l) := by
    intro l
    rw [g2l_psiR, g2l_psi_map, ← g2l_psi_units]
    congr 1
  have htame : ∀ j l, g2l_Tame φ (g1_leftDeriv (g2l_hypZ j)) W (g2l_psiR Qs w l) (gl l) := by
    intro j l
    refine ⟨hval l, ?_, fun Y hY => ?_⟩
    · have hder := g2l_derivation_psi (g1_leftDeriv (g2l_hypZ j))
        ((hQs l).map (C : ℂ →+* MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ))
        (fun i a b => by simp [MvPolynomial.derivation_C]) w _ _ (if l = j then 1 else 0)
        (g2l_leftDeriv_hypZ_t j l) (g2l_leftDeriv_hypZ_u j l)
      rw [← g2l_psiR] at hder
      rw [hder, Matrix.map_smul' _ _ _ (map_mul φ), Matrix.map_mul, hval l, g2l_frameD_map,
        Matrix.mul_smul, ← Matrix.mul_assoc]
      rw [show (((gl l)⁻¹ : Matrix.GeneralLinearGroup (Fin n) _) : Matrix (Fin n) (Fin n) _) *
          g2l_torusAt (QS l) w (τ l) = 1 by
        rw [← g2l_torusUnit_val (hQS l) w (τ l)]
        exact congrArg Units.val (inv_mul_cancel (gl l)), Matrix.one_mul]
      refine Submodule.smul_mem _ _ ?_
      have : g2l_frameD (fun i => ((Qs l i).map C).map φ) w =
          (g2l_frameD (Qs l) w).map (algebraMap ℂ _) := by
        rw [g2l_frameD_map]
        congr 1
      rw [this]
      exact g2l_map_mem_spanS (hD l)
    · rw [g2l_torusUnit_inv_val (hQS l) w (τ l), g2l_torusUnit_val]
      exact g2l_conj_mem_spanS (hQs l) w W (hW l) (τ l) hY
  have htameM : ∀ j, g2l_Tame φ (g1_leftDeriv (g2l_hypZ j)) W (g2l_muR Qs w)
      (List.ofFn gl).prod := fun j => g2l_tame_prod φ _ W _ gl (htame j)
  -- a basis of `W`
  set r := Module.finrank ℂ W
  let bW := Module.finBasis ℂ W
  let Xq : Fin r → Matrix (Fin n) (Fin n) ℂ := fun q => (bW q : Matrix (Fin n) (Fin n) ℂ)
  have hWS : g2l_spanS (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P) W ≤
      Submodule.span _ (Set.range fun q => (Xq q).map (algebraMap ℂ _)) := by
    rw [g2l_spanS, Submodule.span_le]
    rintro _ ⟨Z, hZ, rfl⟩
    have hZsum : Z = ∑ q, (bW.repr ⟨Z, hZ⟩ q) • Xq q := by
      have := congrArg Subtype.val (bW.sum_repr ⟨Z, hZ⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have h := map_sum (algebraMap ℂ (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P)).mapMatrix
      (fun q => (bW.repr ⟨Z, hZ⟩ q) • Xq q) Finset.univ
    simp only [RingHom.mapMatrix_apply] at h
    simp only [SetLike.mem_coe]
    rw [hZsum, h]
    refine Submodule.sum_mem _ fun q _ => ?_
    rw [Matrix.map_smul' _ _ _ (map_mul _)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  set gM := (List.ofFn gl).prod
  have hcoef : ∀ j : Fin N, ∃ a : Fin r → MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P,
      ∑ q, a q • (Xq q).map (algebraMap ℂ _) =
        ((gM⁻¹ : Matrix.GeneralLinearGroup (Fin n) _) : Matrix (Fin n) (Fin n) _) *
          (((g2l_muR Qs w).map (g1_leftDeriv (g2l_hypZ j))).map φ) := fun j =>
    (Submodule.mem_span_range_iff_exists_fun _).mp (hWS (htameM j).2.1)
  choose a ha using hcoef
  choose c hc using fun j q => Ideal.Quotient.mk_surjective (I := P) (a j q)
  have hMbar : (g2l_muR Qs w).map φ = (gM : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P)) := by
    have h1 := map_list_prod φ.mapMatrix (List.ofFn (g2l_psiR Qs w))
    have h2 := map_list_prod (Units.coeHom (Matrix (Fin n) (Fin n)
      (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P))) (List.ofFn gl)
    simp only [RingHom.mapMatrix_apply, List.map_ofFn, Units.coeHom_apply] at h1 h2
    rw [g2l_muR, h1, h2]
    congr 1
    congr 1
    funext l
    exact hval l
  have hrel0 : ∀ j (f : MvPolynomial (Fin n × Fin n) ℂ),
      φ (g1_leftDeriv (g2l_hypZ j) (μ f)) = ∑ q, a j q * φ (μ (g1_leftDeriv (Xq q) f)) := by
    intro j f
    have hB : ((g2l_muR Qs w).map (g1_leftDeriv (g2l_hypZ j))).map φ =
        (gM : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P)) * ∑ q, a j q • (Xq q).map (algebraMap ℂ _) := by
      rw [ha j, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul]
    have h1 : g1_leftDeriv (g2l_hypZ j) (μ f) = ∑ ab : Fin n × Fin n, μ (pderiv ab f) *
        g1_leftDeriv (g2l_hypZ j) (g2l_muR Qs w ab.1 ab.2) :=
      g1s_derivation_aeval _ (fun ab : Fin n × Fin n => g2l_muR Qs w ab.1 ab.2) f
    have h2 : ∀ q, φ (μ (g1_leftDeriv (Xq q) f)) = ∑ ab : Fin n × Fin n, φ (μ (pderiv ab f)) *
        ((gM : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P)) * (Xq q).map (algebraMap ℂ (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P)) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P)) ab.1 ab.2 := by
      intro q
      rw [g2l_leftDeriv_eq_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun ab _ => ?_
      rw [map_mul, map_mul, ← hMbar, Matrix.mul_apply, map_sum, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [μ, g2l_muStar, map_mul, aeval_X, aeval_C, Matrix.map_apply]
      rfl
    have h3 : ∀ ab : Fin n × Fin n, φ (g1_leftDeriv (g2l_hypZ j) (g2l_muR Qs w ab.1 ab.2)) =
        ∑ q, a j q * ((gM : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P)) * (Xq q).map (algebraMap ℂ (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P)) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P)) ab.1 ab.2 := by
      intro ab
      have := congrArg (fun M : Matrix (Fin n) (Fin n) _ => M ab.1 ab.2) hB
      simp only [Matrix.map_apply] at this
      rw [this, Matrix.mul_sum, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    rw [h1, map_sum]
    simp_rw [h2, map_mul, h3, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun ab _ => ?_
    ring
  -- Noether normalization of `ℂ[x] ⧸ I`
  have : Algebra.FiniteType ℂ (MvPolynomial (Fin n × Fin n) ℂ ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ I) (Ideal.Quotient.mkₐ_surjective ℂ I)
  obtain ⟨d, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg ℂ (MvPolynomial (Fin n × Fin n) ℂ ⧸ I)
  have hdim := g2l_ringKrullDim_eq_of_finite_inj g hg hfinite
  choose f hf using fun i : Fin d => Ideal.Quotient.mk_surjective (I := I) (g (X i))
  have hy : AlgebraicIndependent ℂ fun i => Ideal.Quotient.mk P (μ (f i)) := by
    refine algebraicIndependent_iff.mpr fun F hF => ?_
    have h1 : Ideal.Quotient.mk P (μ (aeval f F)) = 0 := by
      rw [← hF, ← Ideal.Quotient.mkₐ_eq_mk ℂ, comp_aeval_apply, comp_aeval_apply]
    have h2 : aeval f F ∈ I := by
      rw [← hPI, Ideal.mem_comap]
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    have h3 : g F = 0 := by
      have : Ideal.Quotient.mk I (aeval f F) = g F := by
        rw [← Ideal.Quotient.mkₐ_eq_mk ℂ, comp_aeval_apply]
        have hfi : (fun i => Ideal.Quotient.mkₐ ℂ I (f i)) = fun i => g (X i) :=
          funext fun i => by rw [Ideal.Quotient.mkₐ_eq_mk, hf i]
        rw [hfi, ← comp_aeval_apply, aeval_X_left_apply]
      rw [← this, Ideal.Quotient.eq_zero_iff_mem]
      exact h2
    exact hg (h3.trans (map_zero g).symm)
  have hδ : ∀ j, ∀ x ∈ P, g1_leftDeriv (g2l_hypZ j) x ∈ P := fun j =>
    g1s_derivation_mem_of_mem_minimalPrimes hrad hPmin _
      (fun x hx => g1_leftDeriv_mem_vanishingIdeal _ (g2l_hypZ_mem j) hx)
  have hdet : (Matrix.of fun j l => g1_leftDeriv (g2l_hypZ j)
      (X (Fin.castAdd N l, Fin.castAdd N l) : MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ)).det ∉ P := by
    have hM : (Matrix.of fun j l => g1_leftDeriv (g2l_hypZ j)
        (X (Fin.castAdd N l, Fin.castAdd N l) : MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ)) =
        Matrix.diagonal fun l => X (Fin.castAdd N l, Fin.castAdd N l) := by
      ext j l
      rw [Matrix.of_apply, g2l_leftDeriv_hypZ_t, Matrix.diagonal_apply]
      by_cases h : j = l
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [hM, Matrix.det_diagonal]
    intro hmem
    obtain ⟨l, -, hl⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    have := htu l
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hl, zero_mul] at this
    exact zero_ne_one this
  have htr : ∀ (J : Type) [Fintype J] (z : J → MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P),
      AlgebraicIndependent ℂ z → Fintype.card J ≤ N := by
    intro J _ z hz
    have : Algebra.FiniteType ℂ (MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ ⧸ P) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) (Ideal.Quotient.mkₐ_surjective ℂ P)
    have h1 := g1s_le_ringKrullDim_of_algebraicIndependent
      (hz.comp (Fintype.equivFin J).symm (Fintype.equivFin J).symm.injective)
    have h2 := ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIXP)
      (Ideal.Quotient.factor_surjective hIXP)
    have h3 := (h1.trans h2).trans g2l_ringKrullDim_hyp_le
    exact_mod_cast h3
  have hrel : ∀ j i, g1_leftDeriv (g2l_hypZ j) (μ (f i)) -
      ∑ q, c j q * μ (g1_leftDeriv (Xq q) (f i)) ∈ P := by
    intro j i
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_sum]
    change φ _ = ∑ q, φ _
    rw [hrel0 j (f i)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, hc j q]
  have key := g2l_card_le_of_jacobian P (fun j => g1_leftDeriv (g2l_hypZ j)) hδ
    (fun l => (X (Fin.castAdd N l, Fin.castAdd N l) :
      MvPolynomial (Fin (N + N) × Fin (N + N)) ℂ)) hdet htr (fun i => μ (f i)) hy c
    (fun q i => μ (g1_leftDeriv (Xq q) (f i))) hrel
  rw [hdim]
  exact_mod_cast key

end Dim

section Irred

set_option warn.classDefReducibility false in
attribute [local instance] g1_zariski

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℤ)

theorem g2l_Gamma_succ {N : ℕ} {Qs : Fin (N + 1) → ι → Matrix (Fin n) (Fin n) ℂ}
    (hQs : ∀ l, g2l_IsFrame (Qs l)) :
    g2l_Gamma w hQs = Set.range (g2l_torusGL (hQs 0) w) *
      g2l_Gamma (Qs := fun l => Qs l.succ) w (fun l => hQs l.succ) := by
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨_, ⟨t 0, rfl⟩, _, ⟨fun l => t l.succ, rfl⟩, ?_⟩
    simp [g2l_prodTorus, List.ofFn_succ]
  · rintro ⟨_, ⟨t₀, rfl⟩, _, ⟨t, rfl⟩, rfl⟩
    refine ⟨Fin.cons t₀ t, ?_⟩
    simp [g2l_prodTorus, List.ofFn_succ]

theorem g2l_isIrreducible_Gamma {N : ℕ} {Qs : Fin N → ι → Matrix (Fin n) (Fin n) ℂ}
    (hQs : ∀ l, g2l_IsFrame (Qs l)) : IsIrreducible (g2l_Gamma w hQs) := by
  induction N with
  | zero =>
    have : g2l_Gamma w hQs = {1} := by
      ext g
      constructor
      · rintro ⟨t, rfl⟩; simp [g2l_prodTorus]
      · rintro rfl; exact ⟨fun l => l.elim0, by simp [g2l_prodTorus]⟩
    rw [this]
    exact isIrreducible_singleton
  | succ N ih =>
    rw [g2l_Gamma_succ w hQs]
    exact g2l_isIrreducible_mul (g2l_isIrreducible_torus (hQs 0) w) (ih _)

theorem g2l_vanishingIdealSet_Gamma_isPrime {N : ℕ}
    {Qs : Fin N → ι → Matrix (Fin n) (Fin n) ℂ} (hQs : ∀ l, g2l_IsFrame (Qs l)) :
    (g1_vanishingIdealSet (g2l_Gamma w hQs)).IsPrime :=
  g1_vanishingIdealSet_isPrime _ (g2l_isIrreducible_Gamma w hQs)

end Irred

end HodgeLean.Foundations
