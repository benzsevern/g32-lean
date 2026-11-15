import HodgeLean.Adapters.IntersectionProductMovingDiagonal
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # The algebra of a family of translates of a cone

Let `B₀ = ℂ[x_σ]` be the homogeneous coordinate ring of `ℙᴺ`, `I_X` and `I_C` homogeneous primes
(a variety `X` and a cone `C`), `M` an `(N+1) × (N+1)` matrix, and `h_t = (1 - t) I + t M`. The
family of translates `t ↦ h_t⁻¹ C` over the open set `det h_t ≠ 0` of the line has, in
`B₀[t]`, the prime ideal `a3m_famIdeal = ker (B₀[t] → (B₀/I_C)[t][1/det h_t], x ↦ h_t⁻¹ x)`.
It contains `F(h_t x)` for every `F ∈ I_C`, its fibre at `t = 0` lies in `V(I_C)` and at `t = 1`
in `V(F(M x) | F ∈ I_C)`, and its dimension is at least `dim B₀/I_C + 1`.

Combined with Serre's dimension inequality in the polynomial ring `B₀[t]` and Krull's principal
ideal theorem, every component of `V(I_X) ∩ V(a3m_famIdeal)` through a point of
`(V(I_X) ∩ V(I_C)) × {0}` has the expected dimension and dominates the line, provided the fibres
of `V(I_X) ∩ V(I_C)` have the expected dimension (`a3m_family_components`).

Source: J. Roberts, *Chow's moving lemma* (1972), §2; Fulton, *Intersection Theory*, second
edition, §1.6 and Example 11.4.1; Serre, *Algèbre locale, multiplicités*, Chapitre V,
Théorème 3; Mathlib, `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Ideal Polynomial

namespace HodgeLean.Adapters

/-! ## Dimension of finite-type domains -/

/-- For finite-type domains over a field, an injective algebra map does not decrease the Krull
dimension (both are transcendence degrees).
Source: Matsumura, *Commutative Ring Theory*, Theorem 5.6; Mathlib, `Algebra.trdeg_le_of_injective`. -/
theorem a3m_ringKrullDim_le_of_injective {k A A' : Type} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [CommRing A'] [IsDomain A'] [Algebra k A']
    [Algebra.FiniteType k A'] (f : A →ₐ[k] A') (hf : Function.Injective f) :
    ringKrullDim A ≤ ringKrullDim A' := by
  obtain ⟨n, hn, hnt⟩ := Algebra.FiniteType.exists_ringKrullDim_eq_and_trdeg_eq (k := k) (A := A)
  obtain ⟨m, hm, hmt⟩ := Algebra.FiniteType.exists_ringKrullDim_eq_and_trdeg_eq (k := k) (A := A')
  have h := trdeg_le_of_injective f hf
  rw [hnt, hmt] at h
  rw [hn, hm]
  exact_mod_cast h

/-- The dimension of a cone: if `φ : B → D[λ]` (with `B`, `D` finite-type domains over `ℂ`) sends
`x_j` to `λ` and hits `s λ^e` for every `s ∈ D`, then `dim B/ker φ = dim D + 1`.
Source: Hartshorne, *Algebraic Geometry*, I, Exercise 2.6 (dimension of the affine cone);
Mathlib, `Algebra.trdeg_add_eq`, `Polynomial.trdeg_of_isDomain`. -/
theorem a3m_ringKrullDim_cone {B D : Type} [CommRing B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    [CommRing D] [IsDomain D] [Algebra ℂ D] [Algebra.FiniteType ℂ D] (φ : B →ₐ[ℂ] D[X])
    (x : B) (hx : φ x = Polynomial.X)
    (hφ : ∀ s : D, ∃ (G : B) (e : ℕ), φ G = Polynomial.C s * Polynomial.X ^ e) :
    ringKrullDim (B ⧸ RingHom.ker φ) = ringKrullDim D + 1 := by
  set E := φ.range
  have hEB : ringKrullDim (B ⧸ RingHom.ker φ) = ringKrullDim E :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange φ).toRingEquiv
  rw [hEB]
  have : Algebra.FiniteType ℂ E := Algebra.FiniteType.of_surjective φ.rangeRestrict
    φ.rangeRestrict_surjective
  have : IsDomain E := inferInstance
  obtain ⟨n, hn, hnt⟩ := Algebra.FiniteType.exists_ringKrullDim_eq_and_trdeg_eq (k := ℂ) (A := E)
  obtain ⟨m, hm, hmt⟩ := Algebra.FiniteType.exists_ringKrullDim_eq_and_trdeg_eq (k := ℂ) (A := D)
  rw [hn, hm]
  -- `D[λ]` is algebraic over `E`
  have hX0 : (Polynomial.X : D[X]) ∈ E := ⟨x, hx⟩
  have halg : Algebra.IsAlgebraic E D[X] := by
    have htop : Algebra.adjoin E (Set.range (Polynomial.C : D → D[X])) = ⊤ := by
      refine eq_top_iff.2 fun f _ => ?_
      rw [← Polynomial.sum_C_mul_X_pow_eq f, Polynomial.sum]
      refine Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _
        (Algebra.subset_adjoin ⟨_, rfl⟩) (Subalgebra.pow_mem _ ?_ _)
      exact (Algebra.adjoin E _).algebraMap_mem (⟨Polynomial.X, hX0⟩ : E)
    have hadj : (Algebra.adjoin E (Set.range (Polynomial.C : D → D[X]))).IsAlgebraic := by
      rw [Algebra.isAlgebraic_adjoin_iff]
      rintro _ ⟨s, rfl⟩
      obtain ⟨G, e, hG⟩ := hφ s
      refine ⟨Polynomial.C (⟨Polynomial.X ^ e, Subalgebra.pow_mem _ hX0 _⟩ : E) * Polynomial.X -
        Polynomial.C (⟨φ G, ⟨G, rfl⟩⟩ : E), ?_, ?_⟩
      · intro h0
        have := congrArg (Polynomial.coeff · 1) h0
        simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
          if_neg one_ne_zero, sub_zero, Polynomial.coeff_zero] at this
        have h2 := congrArg Subtype.val this
        simp only [ZeroMemClass.coe_zero] at h2
        exact pow_ne_zero e Polynomial.X_ne_zero h2
      · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
        change Polynomial.X ^ e * Polynomial.C s - φ G = 0
        rw [hG, mul_comm, sub_self]
    exact ⟨fun f => hadj f (htop ▸ Algebra.mem_top)⟩
  have h1 := trdeg_add_eq ℂ E (A := D[X])
  rw [trdeg_eq_zero (R := E) (A := D[X]), add_zero, hnt] at h1
  have h2 := trdeg_add_eq ℂ D (A := D[X])
  rw [Polynomial.trdeg_of_isDomain, hmt] at h2
  rw [← h2] at h1
  have : (n : Cardinal) = ((m + 1 : ℕ) : Cardinal) := by rw [h1]; push_cast; rfl
  have hnm : n = m + 1 := by exact_mod_cast this
  rw [hnm]
  push_cast
  rfl

/-! ## The family ideal -/

section Family

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- The path `h_t = (1 - t) I + t M` of matrices over `ℂ[t]`. -/
def a3m_hmat (M : Matrix σ σ ℂ) : Matrix σ σ ℂ[X] :=
  (1 - Polynomial.X : ℂ[X]) • (1 : Matrix σ σ ℂ[X]) + (Polynomial.X : ℂ[X]) • M.map Polynomial.C

omit [Fintype σ] in
theorem a3m_hmat_eval_zero (M : Matrix σ σ ℂ) (k l : σ) :
    (a3m_hmat M k l).eval 0 = if k = l then 1 else 0 := by
  simp only [a3m_hmat, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
    smul_eq_mul]
  split_ifs <;> simp

omit [Fintype σ] in
theorem a3m_hmat_eval_one (M : Matrix σ σ ℂ) (k l : σ) : (a3m_hmat M k l).eval 1 = M k l := by
  simp only [a3m_hmat, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply,
    smul_eq_mul]
  split_ifs <;> simp

/-- The substitution `x ↦ h_t x`, from `B₀` to `B₀[t]`. -/
def a3m_subst (M : Matrix σ σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] (MvPolynomial σ ℂ)[X] :=
  MvPolynomial.aeval fun k => ∑ l, Polynomial.map (algebraMap ℂ (MvPolynomial σ ℂ))
    (a3m_hmat M k l) * Polynomial.C (MvPolynomial.X l)

/-- The substitution `x ↦ M x` on `B₀`. -/
def a3m_substM (M : Matrix σ σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  MvPolynomial.aeval fun k => ∑ l, MvPolynomial.C (M k l) * MvPolynomial.X l

theorem a3m_eval_subst (M : Matrix σ σ ℂ) (c : ℂ) (F : MvPolynomial σ ℂ) :
    (a3m_subst M F).eval (MvPolynomial.C c) =
      MvPolynomial.aeval (fun k => ∑ l, MvPolynomial.C ((a3m_hmat M k l).eval c) *
        MvPolynomial.X l) F := by
  have : ((Polynomial.evalRingHom (MvPolynomial.C c)).comp (a3m_subst M).toRingHom :
      MvPolynomial σ ℂ →+* MvPolynomial σ ℂ) =
      (MvPolynomial.aeval (fun k => ∑ l, MvPolynomial.C ((a3m_hmat M k l).eval c) *
        MvPolynomial.X l)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
    · simp [a3m_subst]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, a3m_subst,
        MvPolynomial.aeval_X, coe_evalRingHom, eval_finsetSum, eval_mul, eval_C]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Polynomial.eval_map, ← Polynomial.eval₂_hom, MvPolynomial.algebraMap_eq]
  exact congrArg (fun φ : MvPolynomial σ ℂ →+* MvPolynomial σ ℂ => φ F) this

theorem a3m_eval_zero_subst (M : Matrix σ σ ℂ) (F : MvPolynomial σ ℂ) :
    (a3m_subst M F).eval 0 = F := by
  have h := a3m_eval_subst M 0 F
  rw [map_zero] at h
  have hf : (fun k => ∑ l, MvPolynomial.C ((a3m_hmat M k l).eval 0) * MvPolynomial.X l) =
      (MvPolynomial.X : σ → MvPolynomial σ ℂ) := by
    funext k
    simp [a3m_hmat_eval_zero]
  rw [h, hf, MvPolynomial.aeval_X_left_apply]

theorem a3m_eval_one_subst (M : Matrix σ σ ℂ) (F : MvPolynomial σ ℂ) :
    (a3m_subst M F).eval 1 = a3m_substM M F := by
  have h := a3m_eval_subst M 1 F
  rw [map_one] at h
  have hf : (fun k => ∑ l, MvPolynomial.C ((a3m_hmat M k l).eval 1) * MvPolynomial.X l) =
      (fun k => ∑ l, MvPolynomial.C (M k l) * (MvPolynomial.X l : MvPolynomial σ ℂ)) := by
    funext k
    simp only [a3m_hmat_eval_one]
  rw [h, hf, a3m_substM]

/-- `det h_t`. -/
def a3m_det (M : Matrix σ σ ℂ) : ℂ[X] := (a3m_hmat M).det

theorem a3m_det_eval_zero (M : Matrix σ σ ℂ) : (a3m_det M).eval 0 = 1 := by
  rw [a3m_det, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  have : (Polynomial.evalRingHom 0).mapMatrix (a3m_hmat M) = 1 := by
    ext k l
    simp [a3m_hmat_eval_zero, Matrix.one_apply]
  rw [this, Matrix.det_one]

variable (I_C : Ideal (MvPolynomial σ ℂ)) (M : Matrix σ σ ℂ)

/-- `det h_t` in `(B₀/I_C)[t]`. -/
def a3m_detA : (MvPolynomial σ ℂ ⧸ I_C)[X] :=
  (a3m_det M).map (algebraMap ℂ (MvPolynomial σ ℂ ⧸ I_C))

theorem a3m_detA_ne_zero [hI : I_C.IsPrime] : a3m_detA I_C M ≠ 0 := by
  intro h
  have h1 := congrArg (Polynomial.eval 0) h
  rw [a3m_detA, Polynomial.eval_map, eval_zero,
    show (0 : MvPolynomial σ ℂ ⧸ I_C) = algebraMap ℂ _ 0 from (map_zero _).symm,
    Polynomial.eval₂_hom, a3m_det_eval_zero, map_one, map_zero] at h1
  have : Nontrivial (MvPolynomial σ ℂ ⧸ I_C) := Ideal.Quotient.nontrivial_iff.2 hI.ne_top
  exact one_ne_zero h1

/-- `(B₀/I_C)[t][1/det h_t]`. -/
abbrev a3m_D := Localization.Away (a3m_detA I_C M)

instance a3m_D_isDomain [I_C.IsPrime] : IsDomain (a3m_D I_C M) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (a3m_detA_ne_zero I_C M))

/-- The localization map `(B₀/I_C)[t] → (B₀/I_C)[t][1/det h_t]`. -/
abbrev a3m_ιD : (MvPolynomial σ ℂ ⧸ I_C)[X] →+* a3m_D I_C M :=
  algebraMap (MvPolynomial σ ℂ ⧸ I_C)[X] (a3m_D I_C M)

/-- `x ↦ h_t⁻¹ x = adj(h_t) x / det h_t`, from `B₀` to `(B₀/I_C)[t][1/det h_t]`. -/
def a3m_famHom₀ : MvPolynomial σ ℂ →+* a3m_D I_C M :=
  MvPolynomial.eval₂Hom (algebraMap ℂ (a3m_D I_C M)) fun k =>
    (∑ l, a3m_ιD I_C M (((a3m_hmat M).adjugate k l).map
        (algebraMap ℂ (MvPolynomial σ ℂ ⧸ I_C))) *
      a3m_ιD I_C M (Polynomial.C (Ideal.Quotient.mk I_C (MvPolynomial.X l)))) *
    IsLocalization.Away.invSelf (a3m_detA I_C M)

/-- The map `B₀[t] → (B₀/I_C)[t][1/det h_t]`, `x ↦ h_t⁻¹ x`, `t ↦ t`. -/
def a3m_famHom : (MvPolynomial σ ℂ)[X] →+* a3m_D I_C M :=
  Polynomial.eval₂RingHom (a3m_famHom₀ I_C M) (a3m_ιD I_C M Polynomial.X)

/-- The ideal of the closure of the family of translates `h_t⁻¹ V(I_C)`, `det h_t ≠ 0`.
Source: Fulton, *Intersection Theory*, second edition, §1.6 (families over the line);
J. Roberts, *Chow's moving lemma* (1972), §2. -/
def a3m_famIdeal : Ideal (MvPolynomial σ ℂ)[X] := RingHom.ker (a3m_famHom I_C M)

instance a3m_famIdeal_isPrime [I_C.IsPrime] : (a3m_famIdeal I_C M).IsPrime :=
  RingHom.ker_isPrime _

theorem a3m_famHom_map (h : ℂ[X]) :
    a3m_famHom I_C M (h.map (algebraMap ℂ (MvPolynomial σ ℂ))) =
      a3m_ιD I_C M (h.map (algebraMap ℂ (MvPolynomial σ ℂ ⧸ I_C))) := by
  rw [a3m_famHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map]
  conv_rhs => rw [← Polynomial.eval₂_C_X (p := h.map _), Polynomial.eval₂_map,
    Polynomial.hom_eval₂]
  congr 1
  ext c
  simp [a3m_famHom₀, IsScalarTower.algebraMap_apply ℂ (MvPolynomial σ ℂ ⧸ I_C)[X]
    (a3m_D I_C M)]

theorem a3m_famHom_subst :
    (a3m_famHom I_C M).comp (a3m_subst M).toRingHom =
      (a3m_ιD I_C M).comp (Polynomial.C.comp (Ideal.Quotient.mk I_C)) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
  · simp [a3m_subst, a3m_famHom, a3m_famHom₀,
      IsScalarTower.algebraMap_apply ℂ (MvPolynomial σ ℂ ⧸ I_C)[X] (a3m_D I_C M)]
    rfl
  · set ι := a3m_ιD I_C M
    set g := algebraMap ℂ (MvPolynomial σ ℂ ⧸ I_C)
    have key : ∀ m, ∑ l, ι ((a3m_hmat M k l).map g) * ι (((a3m_hmat M).adjugate l m).map g) =
        if k = m then ι (a3m_detA I_C M) else 0 := by
      intro m
      simp_rw [← map_mul, ← Polynomial.map_mul, ← map_sum, ← Polynomial.map_sum]
      rw [← Matrix.mul_apply, Matrix.mul_adjugate]
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      split_ifs <;> simp [a3m_detA, a3m_det, g]
    have hX : a3m_famHom I_C M (Polynomial.C (MvPolynomial.X k)) = a3m_famHom₀ I_C M
        (MvPolynomial.X k) := by
      simp [a3m_famHom]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, a3m_subst,
      MvPolynomial.aeval_X, map_sum, map_mul]
    rw [Finset.sum_congr rfl fun l _ => by rw [a3m_famHom_map]]
    simp only [a3m_famHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    simp only [a3m_famHom₀, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    set c := fun l => ι (Polynomial.C ((Ideal.Quotient.mk I_C) (MvPolynomial.X l)))
    set inv := IsLocalization.Away.invSelf (S := a3m_D I_C M) (a3m_detA I_C M)
    have h1 : ∀ x, ι ((a3m_hmat M k x).map g) * ((∑ l, ι (((a3m_hmat M).adjugate x l).map g) *
        c l) * inv) = ∑ l, ι ((a3m_hmat M k x).map g) * ι (((a3m_hmat M).adjugate x l).map g) *
          c l * inv := by
      intro x
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    change ∑ x, ι ((a3m_hmat M k x).map g) * ((∑ l, ι (((a3m_hmat M).adjugate x l).map g) *
        c l) * inv) = c k
    rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_comm]
    have h2 : ∀ l, ∑ x, ι ((a3m_hmat M k x).map g) * ι (((a3m_hmat M).adjugate x l).map g) *
        c l * inv = (if k = l then ι (a3m_detA I_C M) else 0) * c l * inv := by
      intro l
      rw [← key l, Finset.sum_mul, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun l _ => h2 l]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [mul_comm (ι _) (c k), mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]


/-- `F(h_t x) ∈ a3m_famIdeal` for `F ∈ I_C`. -/
theorem a3m_subst_mem_famIdeal {F : MvPolynomial σ ℂ} (hF : F ∈ I_C) :
    a3m_subst M F ∈ a3m_famIdeal I_C M := by
  rw [a3m_famIdeal, RingHom.mem_ker]
  have := congrArg (fun φ : MvPolynomial σ ℂ →+* a3m_D I_C M => φ F) (a3m_famHom_subst I_C M)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this, Ideal.Quotient.eq_zero_iff_mem.2 hF, Polynomial.C_0, map_zero]

/-- The fibre of the family at `t = 0` lies in `V(I_C)`. -/
theorem a3m_eval_zero_mem_of_mem_famIdeal [I_C.IsPrime] {G : (MvPolynomial σ ℂ)[X]}
    (hG : G ∈ a3m_famIdeal I_C M) : G.eval 0 ∈ I_C := by
  set A := MvPolynomial σ ℂ ⧸ I_C
  have hu : IsUnit ((Polynomial.evalRingHom (0 : A)) (a3m_detA I_C M)) := by
    rw [Polynomial.coe_evalRingHom, a3m_detA, Polynomial.eval_map,
      show (0 : A) = algebraMap ℂ A 0 from (map_zero _).symm, Polynomial.eval₂_hom,
      a3m_det_eval_zero, map_one]
    exact isUnit_one
  set ε : a3m_D I_C M →+* A := IsLocalization.Away.lift (a3m_detA I_C M) hu
  have hει : ∀ p, ε (a3m_ιD I_C M p) = p.eval 0 := fun p =>
    IsLocalization.Away.lift_eq _ hu p
  have hεinv : ε (IsLocalization.Away.invSelf (a3m_detA I_C M)) = 1 := by
    have h := congrArg ε (IsLocalization.Away.mul_invSelf (S := a3m_D I_C M) (a3m_detA I_C M))
    rw [map_mul, map_one] at h
    change ε (a3m_ιD I_C M _) * _ = 1 at h
    rw [hει] at h
    have h0 : (a3m_detA I_C M).eval 0 = 1 := by
      have := hu
      rw [a3m_detA, Polynomial.eval_map,
        show (0 : A) = algebraMap ℂ A 0 from (map_zero _).symm, Polynomial.eval₂_hom,
        a3m_det_eval_zero, map_one]
    rwa [h0, one_mul] at h
  have hadj : ∀ k l, ((a3m_hmat M).adjugate k l).eval 0 = if k = l then 1 else 0 := by
    intro k l
    have := congrArg (fun A => A k l) ((Polynomial.evalRingHom (0 : ℂ)).map_adjugate (a3m_hmat M))
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Polynomial.coe_evalRingHom] at this
    rw [this]
    have h1 : (a3m_hmat M).map (Polynomial.eval 0) = 1 := by
      ext a b
      simp [a3m_hmat_eval_zero, Matrix.one_apply]
    rw [h1, Matrix.adjugate_one, Matrix.one_apply]
  have hcomp₀ : ε.comp (a3m_famHom₀ I_C M) = Ideal.Quotient.mk I_C := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
    · simp only [RingHom.comp_apply, a3m_famHom₀, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_C, IsScalarTower.algebraMap_apply ℂ A[X] (a3m_D I_C M)]
      rw [show algebraMap A[X] (a3m_D I_C M) = a3m_ιD I_C M from rfl, hει,
        Polynomial.algebraMap_apply, Polynomial.eval_C]
      rfl
    · simp only [RingHom.comp_apply, a3m_famHom₀, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_X, map_mul, map_sum, hει, hεinv, mul_one, Polynomial.eval_zero_map,
        Polynomial.eval_C, hadj]
      simp
  have hcomp : ε.comp (a3m_famHom I_C M) =
      (Ideal.Quotient.mk I_C).comp (Polynomial.evalRingHom 0) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.comp_apply, a3m_famHom, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, Polynomial.coe_evalRingHom, Polynomial.eval_C]
      exact congrArg (fun φ : MvPolynomial σ ℂ →+* A => φ a) hcomp₀
    · simp only [RingHom.comp_apply, a3m_famHom, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, Polynomial.coe_evalRingHom, Polynomial.eval_X, map_zero, hει]
  have := congrArg (fun φ : (MvPolynomial σ ℂ)[X] →+* A => φ G) hcomp
  simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom] at this
  rw [a3m_famIdeal, RingHom.mem_ker] at hG
  rw [hG, map_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm

/-- The family has dimension at least `dim B₀/I_C + 1`: `(B₀/I_C)[t]` embeds into its
coordinate ring through `x ↦ h_t x`. -/
theorem a3m_ringKrullDim_famIdeal [I_C.IsPrime] :
    ringKrullDim (MvPolynomial σ ℂ ⧸ I_C) + 1 ≤
      ringKrullDim ((MvPolynomial σ ℂ)[X] ⧸ a3m_famIdeal I_C M) := by
  set A := MvPolynomial σ ℂ ⧸ I_C
  set Q := (MvPolynomial σ ℂ)[X] ⧸ a3m_famIdeal I_C M
  let ψ₀ : A →+* Q := Ideal.Quotient.lift I_C
    ((Ideal.Quotient.mk _).comp (a3m_subst M).toRingHom) fun F hF =>
      Ideal.Quotient.eq_zero_iff_mem.2 (a3m_subst_mem_famIdeal I_C M hF)
  let ψ : A[X] →+* Q := Polynomial.eval₂RingHom ψ₀ (Ideal.Quotient.mk _ Polynomial.X)
  let κ : Q →+* a3m_D I_C M := RingHom.kerLift (a3m_famHom I_C M)
  have hκψ : κ.comp ψ = a3m_ιD I_C M := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [RingHom.comp_apply]
      have h1 : ψ (Polynomial.C (Ideal.Quotient.mk I_C F)) = ψ₀ (Ideal.Quotient.mk I_C F) :=
        Polynomial.eval₂_C _ _
      have h2 : ψ₀ (Ideal.Quotient.mk I_C F) = Ideal.Quotient.mk _ (a3m_subst M F) :=
        Ideal.Quotient.lift_mk _ _ _
      rw [h1, h2]
      change a3m_famHom I_C M (a3m_subst M F) = _
      exact congrArg (fun φ : MvPolynomial σ ℂ →+* a3m_D I_C M => φ F) (a3m_famHom_subst I_C M)
    · rw [RingHom.comp_apply]
      have h1 : ψ Polynomial.X = Ideal.Quotient.mk _ Polynomial.X := Polynomial.eval₂_X _ _
      rw [h1]
      change a3m_famHom I_C M Polynomial.X = _
      exact Polynomial.eval₂_X _ _
  have hι : Function.Injective (a3m_ιD I_C M) :=
    IsLocalization.injective (a3m_D I_C M)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (a3m_detA_ne_zero I_C M))
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply hι
    rw [← hκψ, RingHom.comp_apply, RingHom.comp_apply, hab]
  let ψa : A[X] →ₐ[ℂ] Q :=
    { ψ with
      commutes' := fun c => by
        change ψ (algebraMap ℂ A[X] c) = _
        rw [Polynomial.algebraMap_apply]
        have h1 : ψ (Polynomial.C (algebraMap ℂ A c)) = ψ₀ (algebraMap ℂ A c) :=
          Polynomial.eval₂_C _ _
        rw [h1, show algebraMap ℂ A c = Ideal.Quotient.mk I_C (algebraMap ℂ _ c) from rfl]
        change Ideal.Quotient.mk _ (a3m_subst M (algebraMap ℂ _ c)) = _
        rw [AlgHom.commutes]
        rfl }
  have : Algebra.FiniteType ℂ Q :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have h := a3m_ringKrullDim_le_of_injective (k := ℂ) ψa hψ
  rwa [Polynomial.ringKrullDim_of_isNoetherianRing] at h

end Family

/-! ## Components of the family -/

section Components

variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem a3m_ringKrullDim_B : ringKrullDim (MvPolynomial σ ℂ)[X] = (Fintype.card σ + 1 : ℕ) := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_fintype_card]
  simp

/-- The dimension formula in `B₀[t]`. -/
theorem a3m_height_add_dim_B (J : Ideal (MvPolynomial σ ℂ)[X]) [J.IsPrime] :
    (J.height : WithBot ℕ∞) + ringKrullDim ((MvPolynomial σ ℂ)[X] ⧸ J) =
      (Fintype.card σ + 1 : ℕ) := by
  rw [hc9k8_height_add_ringKrullDim_quotient (k := ℂ) J, a3m_ringKrullDim_B]

theorem a3m_ringKrullDim_map_C (I : Ideal (MvPolynomial σ ℂ)) :
    ringKrullDim ((MvPolynomial σ ℂ)[X] ⧸ (Ideal.map Polynomial.C I : Ideal _)) =
      ringKrullDim (MvPolynomial σ ℂ ⧸ I) + 1 := by
  rw [← ringKrullDim_eq_of_ringEquiv (Ideal.polynomialQuotientEquivQuotientPolynomial I),
    Polynomial.ringKrullDim_of_isNoetherianRing]

/-- `G ≡ G(0) mod t`. -/
theorem a3m_sub_C_eval_zero_mem (G : (MvPolynomial σ ℂ)[X]) :
    G - Polynomial.C (G.eval 0) ∈ Ideal.span {(Polynomial.X : (MvPolynomial σ ℂ)[X])} := by
  rw [Ideal.mem_span_singleton, ← Polynomial.coeff_zero_eq_eval_zero]
  exact Polynomial.X_dvd_sub_C

variable (I_X I_C : Ideal (MvPolynomial σ ℂ)) [I_X.IsPrime] [I_C.IsPrime] (M : Matrix σ σ ℂ)

/-- The ideal of the intersection of `V(I_X) × 𝔸¹` with the family. -/
def a3m_famInter : Ideal (MvPolynomial σ ℂ)[X] :=
  Ideal.map Polynomial.C I_X ⊔ a3m_famIdeal I_C M

/-- A prime of `B₀[t]` containing the family ideal and `t` is the cone over a point of
`V(I_X + I_C)`, so its dimension is bounded by the fibre bound. -/
theorem a3m_dim_le_of_X_mem (d : ℕ)
    (hfib : ∀ p : Ideal (MvPolynomial σ ℂ), p.IsPrime → I_X ⊔ I_C ≤ p →
      ringKrullDim (MvPolynomial σ ℂ ⧸ p) ≤ (d + 1 : ℕ))
    (J : Ideal (MvPolynomial σ ℂ)[X]) [hJ : J.IsPrime] (hJa : a3m_famInter I_X I_C M ≤ J)
    (hXJ : (Polynomial.X : (MvPolynomial σ ℂ)[X]) ∈ J) :
    ringKrullDim ((MvPolynomial σ ℂ)[X] ⧸ J) ≤ (d + 1 : ℕ) := by
  let φ : MvPolynomial σ ℂ →+* (MvPolynomial σ ℂ)[X] ⧸ J :=
    (Ideal.Quotient.mk J).comp Polynomial.C
  have hmodX : ∀ G, Ideal.Quotient.mk J G = φ (G.eval 0) := by
    intro G
    rw [RingHom.comp_apply, Ideal.Quotient.eq]
    exact (Ideal.span_singleton_le_iff_mem J).2 hXJ (a3m_sub_C_eval_zero_mem G)
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨G.eval 0, (hmodX G).symm⟩
  have hker : I_X ⊔ I_C ≤ RingHom.ker φ := by
    refine sup_le (fun F hF => ?_) (fun F hF => ?_)
    · rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hJa (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hF))
    · rw [RingHom.mem_ker, ← a3m_eval_zero_subst M F, ← hmodX, Ideal.Quotient.eq_zero_iff_mem]
      exact hJa (Ideal.mem_sup_right (a3m_subst_mem_famIdeal I_C M hF))
  rw [← ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφ)]
  exact hfib _ (RingHom.ker_isPrime φ) hker

/-- The prime of `V(P) × {0}` in `B₀[t]`. -/
def a3m_zeroFibre (P : Ideal (MvPolynomial σ ℂ)) : Ideal (MvPolynomial σ ℂ)[X] :=
  RingHom.ker ((Ideal.Quotient.mk P).comp (Polynomial.evalRingHom 0))

omit [Fintype σ] [DecidableEq σ] in
theorem a3m_mem_zeroFibre (P : Ideal (MvPolynomial σ ℂ)) (G : (MvPolynomial σ ℂ)[X]) :
    G ∈ a3m_zeroFibre P ↔ G.eval 0 ∈ P := by
  rw [a3m_zeroFibre, RingHom.mem_ker, RingHom.comp_apply, Polynomial.coe_evalRingHom,
    Ideal.Quotient.eq_zero_iff_mem]

omit [Fintype σ] [DecidableEq σ] in
instance a3m_zeroFibre_isPrime (P : Ideal (MvPolynomial σ ℂ)) [P.IsPrime] :
    (a3m_zeroFibre P).IsPrime := RingHom.ker_isPrime _

theorem a3m_famInter_le_zeroFibre (P : Ideal (MvPolynomial σ ℂ)) (hP : I_X ⊔ I_C ≤ P) :
    a3m_famInter I_X I_C M ≤ a3m_zeroFibre P := by
  refine sup_le (Ideal.map_le_iff_le_comap.2 fun F hF => ?_) fun G hG => ?_
  · rw [Ideal.mem_comap, a3m_mem_zeroFibre, Polynomial.eval_C]
    exact hP (Ideal.mem_sup_left hF)
  · rw [a3m_mem_zeroFibre]
    exact hP (Ideal.mem_sup_right (a3m_eval_zero_mem_of_mem_famIdeal I_C M hG))

/-- Components of the family through the zero fibre: if `V(I_X)` has dimension `n`, the cone
`V(I_C)` has dimension at least `d + N - n` and every point of `V(I_X) ∩ V(I_C)` has dimension
at most `d`, then every irreducible component of `(V(I_X) × 𝔸¹) ∩ family` through a point of
`(V(I_X) ∩ V(I_C)) × {0}` has dimension `d + 1` (affine cone dimension `d + 2`), does not lie in
the fibre `t = 0`, and dominates the line.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, Théorème 3 (lower bound);
Krull's principal ideal theorem (upper bound); Fulton, *Intersection Theory*, second edition,
§1.6. -/
theorem a3m_family_components (n d : ℕ)
    (hX : ringKrullDim (MvPolynomial σ ℂ ⧸ I_X) = (n + 1 : ℕ))
    (hC : ((d + Fintype.card σ : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℂ ⧸ I_C) + n)
    (hfib : ∀ p : Ideal (MvPolynomial σ ℂ), p.IsPrime → I_X ⊔ I_C ≤ p →
      ringKrullDim (MvPolynomial σ ℂ ⧸ p) ≤ (d + 1 : ℕ))
    (P : Ideal (MvPolynomial σ ℂ)) [P.IsPrime] (Q : Ideal (MvPolynomial σ ℂ)[X])
    (hQ : Q ∈ (a3m_famInter I_X I_C M).minimalPrimes) (hQP : Q ≤ a3m_zeroFibre P) :
    ringKrullDim ((MvPolynomial σ ℂ)[X] ⧸ Q) = (d + 2 : ℕ) ∧
      (Polynomial.X : (MvPolynomial σ ℂ)[X]) ∉ Q ∧
      ∀ f : ℂ[X], f ≠ 0 → f.map (algebraMap ℂ (MvPolynomial σ ℂ)) ∉ Q := by
  have hQp : Q.IsPrime := hQ.1.1
  have hQa : a3m_famInter I_X I_C M ≤ Q := hQ.1.2
  -- the lower bound, from Serre's inequality
  have hS := a3m_height_le_of_mem_minimalPrimes_of_equiv (k := ℂ)
    (MvPolynomial.optionEquivLeft ℂ σ).toRingEquiv (Ideal.map Polynomial.C I_X)
    (a3m_famIdeal I_C M) Q hQ
  have h1 := a3m_height_add_dim_B (Ideal.map Polynomial.C I_X : Ideal (MvPolynomial σ ℂ)[X])
  rw [a3m_ringKrullDim_map_C, hX] at h1
  have h2 := a3m_height_add_dim_B (a3m_famIdeal I_C M)
  have h2' := a3m_ringKrullDim_famIdeal I_C M
  have h3 := a3m_height_add_dim_B Q
  obtain ⟨c, hc, -⟩ := Algebra.FiniteType.exists_ringKrullDim_eq_and_trdeg_eq (k := ℂ)
    (A := MvPolynomial σ ℂ ⧸ I_C)
  rw [hc] at hC h2'
  obtain ⟨a, b, ha, hb, hab⟩ := a3m_withBot_add_eq_nat h1
  obtain ⟨f, g, hf, hg, hfg⟩ := a3m_withBot_add_eq_nat h2
  obtain ⟨q, r, hq, hr, hqr⟩ := a3m_withBot_add_eq_nat h3
  have hb' : b = n + 1 + 1 := by
    have : ((n + 1 + 1 : ℕ) : WithBot ℕ∞) = (b : WithBot ℕ∞) := by
      rw [← hb]; push_cast; rfl
    exact_mod_cast this.symm
  have hg' : c + 1 ≤ g := by
    rw [hg] at h2'
    exact_mod_cast h2'
  have hC' : d + Fintype.card σ ≤ c + n := by exact_mod_cast hC
  have hS' : q ≤ a + f := by
    rw [ha, hf, hq] at hS
    exact_mod_cast hS
  have hlow : d + 2 ≤ r := by omega
  -- `t ∉ Q`
  have hXQ : (Polynomial.X : (MvPolynomial σ ℂ)[X]) ∉ Q := by
    intro hX'
    have := a3m_dim_le_of_X_mem I_X I_C M d hfib Q hQa hX'
    rw [hr] at this
    have : r ≤ d + 1 := by exact_mod_cast this
    omega
  -- the upper bound, from Krull's principal ideal theorem
  have hup : r ≤ d + 2 := by
    set R := (MvPolynomial σ ℂ)[X] ⧸ Q
    set x : R := Ideal.Quotient.mk Q Polynomial.X
    have hne : Ideal.span {x} ≠ ⊤ := by
      intro htop
      let ε : R →+* MvPolynomial σ ℂ ⧸ P := Ideal.Quotient.lift Q
        ((Ideal.Quotient.mk P).comp (Polynomial.evalRingHom 0)) fun z hz => by
          have := hQP hz
          rwa [a3m_zeroFibre, RingHom.mem_ker] at this
      have hu := (Ideal.span_singleton_eq_top.1 htop).map ε
      have h0 : ε x = 0 := by
        change Ideal.Quotient.mk P ((Polynomial.X : (MvPolynomial σ ℂ)[X]).eval 0) = 0
        rw [Polynomial.eval_X, map_zero]
      rw [h0] at hu
      have : Nontrivial (MvPolynomial σ ℂ ⧸ P) :=
        Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
      exact not_isUnit_zero hu
    obtain ⟨N', hN'⟩ := Ideal.nonempty_minimalPrimes hne
    have hN'p : N'.IsPrime := hN'.1.1
    have hht : N'.height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hN'
    set N := N'.comap (Ideal.Quotient.mk Q)
    have hQN : Q ≤ N := fun z hz => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hz]
      exact zero_mem _
    have hXN : Polynomial.X ∈ N := hN'.1.2 (Ideal.mem_span_singleton_self x)
    have hNb := a3m_dim_le_of_X_mem I_X I_C M d hfib N (hQa.trans hQN) hXN
    have hmap : N.map (Ideal.Quotient.mk Q) = N' :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective N'
    have hiso := DoubleQuot.quotQuotEquivQuotOfLE hQN
    rw [hmap] at hiso
    have hdimR := hc9k8_height_add_ringKrullDim_quotient (k := ℂ) N'
    rw [ringKrullDim_eq_of_ringEquiv hiso] at hdimR
    change _ = ringKrullDim ((MvPolynomial σ ℂ)[X] ⧸ Q) at hdimR
    rw [hr] at hdimR
    obtain ⟨s', w, hs', hw, hsw⟩ := a3m_withBot_add_eq_nat hdimR
    rw [hs'] at hht
    rw [hw] at hNb
    have : s' ≤ 1 := by exact_mod_cast hht
    have : w ≤ d + 1 := by exact_mod_cast hNb
    omega
  refine ⟨by rw [hr]; exact_mod_cast le_antisymm hup hlow, hXQ, fun f hf hfQ => ?_⟩
  -- domination: the contraction of `Q` to `ℂ[t]` is a prime inside `(t)`, hence zero
  set ψ : ℂ[X] →+* (MvPolynomial σ ℂ)[X] := Polynomial.mapRingHom (algebraMap ℂ _)
  have hq : (Q.comap ψ).IsPrime := Ideal.comap_isPrime ψ Q
  have hqne : Q.comap ψ ≠ ⊥ := fun h => hf (by
    have : f ∈ Q.comap ψ := hfQ
    rwa [h, Ideal.mem_bot] at this)
  have hmax := Ideal.IsPrime.isMaximal hq hqne
  have hle : Q.comap ψ ≤ (a3m_zeroFibre P).comap ψ := Ideal.comap_mono hQP
  have hne : (a3m_zeroFibre P).comap ψ ≠ ⊤ := by
    intro h
    have : (1 : ℂ[X]) ∈ (a3m_zeroFibre P).comap ψ := h ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one, a3m_mem_zeroFibre, Polynomial.eval_one] at this
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 this)
  have heq := hmax.eq_of_le hne hle
  have hX : (Polynomial.X : ℂ[X]) ∈ (a3m_zeroFibre P).comap ψ := by
    rw [Ideal.mem_comap, a3m_mem_zeroFibre]
    simp [ψ]
  rw [← heq, Ideal.mem_comap] at hX
  exact hXQ (by simpa [ψ] using hX)

end Components

end HodgeLean.Adapters
