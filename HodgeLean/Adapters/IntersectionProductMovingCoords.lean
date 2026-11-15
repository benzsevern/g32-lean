import HodgeLean.Adapters.IntersectionProductDefs

/-! # Points of a scheme with projective charts as homogeneous primes

Let `Y` be a scheme covered by affine opens `U j` (`j : σ`) and let `θ j : R[x_σ] → Γ(Y, U j)` be
ring maps with `θ j (x_j) = 1`, surjective, such that `U j ∩ U l` is the basic open of `θ l (x_j)`
in `U l` and, for `F` homogeneous of degree `e`, `θ l F = (θ l x_j)^e · θ j F` on `U j ∩ U l`.
This is the situation of a closed subscheme of projective space over `R`, with `θ j` the
dehomogenization at `x_j`. Each point `y` then has a homogeneous prime
`a3m_Charts.prime y = {F | the homogeneous components of F vanish at y}`, which is relevant, and
`y ⤳ y'` exactly when `prime y ≤ prime y'`. On an integral `Y` every relevant homogeneous prime
containing the homogeneous ideal of `Y` is of this form.

Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5 (the points of `Proj S` are the
relevant homogeneous primes, and `D₊(x_j) ≅ Spec S_(x_j)`); Stacks Project, Tag 00JP.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace HodgeLean.Adapters

/-- Projective charts on a scheme `Y`: affine opens `U j` and dehomogenizations
`θ j : R[x_σ] → Γ(Y, U j)` at `x_j`, compatible on overlaps.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5. -/
structure a3m_Charts (Y : Scheme.{0}) (σ : Type) (R : Type) [CommRing R] where
  /-- The chart opens. -/
  U : σ → Y.Opens
  affine : ∀ j, IsAffineOpen (U j)
  cover : ∀ y : Y, ∃ j, y ∈ U j
  /-- The dehomogenizations. -/
  θ : ∀ j, MvPolynomial σ R →+* Γ(Y, U j)
  θ_X_self : ∀ j, θ j (X j) = 1
  θ_surj : ∀ j, Function.Surjective (θ j)
  inter : ∀ j l, U j ⊓ U l = Y.basicOpen (θ l (X j))
  compat : ∀ (j l : σ) (F : MvPolynomial σ R) (e : ℕ), F.IsHomogeneous e →
    Y.presheaf.map (homOfLE (inf_le_right : U j ⊓ U l ≤ U l)).op (θ l F) =
      Y.presheaf.map (homOfLE (inf_le_right : U j ⊓ U l ≤ U l)).op (θ l (X j)) ^ e *
        Y.presheaf.map (homOfLE (inf_le_left : U j ⊓ U l ≤ U j)).op (θ j F)

namespace a3m_Charts

variable {Y : Scheme.{0}} {σ : Type} {R : Type} [CommRing R] (C : a3m_Charts Y σ R)

/-- Evaluation commutes with restriction. -/
theorem a3m_evaluation_res {U V : Y.Opens} (h : V ≤ U) (y : Y) (hy : y ∈ V) (s : Γ(Y, U)) :
    Y.evaluation V y hy (Y.presheaf.map (homOfLE h).op s) = Y.evaluation U y (h hy) s := by
  simp only [Scheme.evaluation, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]

/-- The value at `y ∈ U j` in the chart `j`, as a ring map. -/
def ev (j : σ) (y : Y) (hy : y ∈ C.U j) : MvPolynomial σ R →+* Y.residueField y :=
  (Y.evaluation (C.U j) y hy).hom.comp (C.θ j)

theorem ev_apply (j : σ) (y : Y) (hy : y ∈ C.U j) (F : MvPolynomial σ R) :
    C.ev j y hy F = Y.evaluation (C.U j) y hy (C.θ j F) := rfl

/-- On an overlap the values in two charts differ by a power of the nonzero value of `x_j` in
chart `l`. -/
theorem ev_compat (j l : σ) (y : Y) (hj : y ∈ C.U j) (hl : y ∈ C.U l) (F : MvPolynomial σ R)
    (e : ℕ) (hF : F.IsHomogeneous e) :
    C.ev l y hl F = C.ev l y hl (X j) ^ e * C.ev j y hj F := by
  have hjl : y ∈ C.U j ⊓ C.U l := ⟨hj, hl⟩
  have h := congrArg (Y.evaluation (C.U j ⊓ C.U l) y hjl) (C.compat j l F e hF)
  rw [map_mul, map_pow, a3m_evaluation_res, a3m_evaluation_res, a3m_evaluation_res] at h
  exact h

theorem ev_X_ne_zero (j l : σ) (y : Y) (hj : y ∈ C.U j) (hl : y ∈ C.U l) :
    C.ev l y hl (X j) ≠ 0 := by
  rw [ev_apply, Scheme.evaluation_ne_zero_iff_mem_basicOpen, ← C.inter j l]
  exact ⟨hj, hl⟩

theorem ev_X_self (j : σ) (y : Y) (hj : y ∈ C.U j) : C.ev j y hj (X j) = 1 := by
  rw [ev_apply, C.θ_X_self, map_one]

theorem ev_eq_eval₂ (j : σ) (y : Y) (hy : y ∈ C.U j) (F : MvPolynomial σ R) :
    C.ev j y hy F = eval₂ ((C.ev j y hy).comp MvPolynomial.C) (fun k => C.ev j y hy (X k)) F := by
  conv_lhs => rw [← MvPolynomial.eval₂_eta F]
  exact (MvPolynomial.eval₂_comp_left _ _ _ _)

theorem ev_homog_eq_zero_iff (j l : σ) (y : Y) (hj : y ∈ C.U j) (hl : y ∈ C.U l)
    (F : MvPolynomial σ R) (e : ℕ) (hF : F.IsHomogeneous e) :
    C.ev l y hl F = 0 ↔ C.ev j y hj F = 0 := by
  rw [C.ev_compat j l y hj hl F e hF, mul_eq_zero,
    or_iff_right (pow_ne_zero _ (C.ev_X_ne_zero j l y hj hl))]

/-- A chart containing `y`. -/
def chart (y : Y) : σ := (C.cover y).choose

theorem mem_chart (y : Y) : y ∈ C.U (C.chart y) := (C.cover y).choose_spec

variable [Fintype σ]

/-- Evaluation of a homogeneous polynomial at `λ a` is `λ^e` times its value at `a`. -/
theorem a3m_eval₂_mul_X_of_isHomogeneous {S : Type} [CommRing S] (g : R →+* S) (a : σ → S)
    (F : MvPolynomial σ R) (e : ℕ) (hF : F.IsHomogeneous e) :
    eval₂ (Polynomial.C.comp g) (fun k => Polynomial.C (a k) * Polynomial.X) F =
      Polynomial.C (eval₂ g a F) * Polynomial.X ^ e := by
  rw [eval₂_eq', eval₂_eq', map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  have hd : ∑ i, m i = e := by
    rw [← hF (MvPolynomial.mem_support_iff.mp hm)]
    simp only [Finsupp.weight_apply, smul_eq_mul, Pi.one_apply, mul_one]
    exact (Finsupp.sum_fintype m (fun _ x ↦ x) (fun _ ↦ rfl)).symm
  simp only [RingHom.coe_comp, Function.comp_apply, mul_pow, Finset.prod_mul_distrib, map_mul,
    map_prod, map_pow]
  rw [Finset.prod_pow_eq_pow_sum, hd]
  ring

/-- The graded value of a polynomial at `y`: `F ↦ Σ_e F_e(y) λ^e`. -/
def lam (j : σ) (y : Y) (hy : y ∈ C.U j) : MvPolynomial σ R →+* Polynomial (Y.residueField y) :=
  eval₂Hom (Polynomial.C.comp ((C.ev j y hy).comp MvPolynomial.C))
    (fun k => Polynomial.C (C.ev j y hy (X k)) * Polynomial.X)

theorem lam_of_isHomogeneous (j : σ) (y : Y) (hy : y ∈ C.U j) (F : MvPolynomial σ R) (e : ℕ)
    (hF : F.IsHomogeneous e) :
    C.lam j y hy F = Polynomial.C (C.ev j y hy F) * Polynomial.X ^ e := by
  rw [lam, coe_eval₂Hom, a3m_eval₂_mul_X_of_isHomogeneous _ _ F e hF, ← ev_eq_eval₂]

theorem lam_eq_sum (j : σ) (y : Y) (hy : y ∈ C.U j) (F : MvPolynomial σ R) :
    C.lam j y hy F = ∑ e ∈ Finset.range (F.totalDegree + 1),
      Polynomial.C (C.ev j y hy (homogeneousComponent e F)) * Polynomial.X ^ e := by
  conv_lhs => rw [← sum_homogeneousComponent F]
  rw [map_sum]
  exact Finset.sum_congr rfl fun e _ =>
    C.lam_of_isHomogeneous j y hy _ e (homogeneousComponent_isHomogeneous e F)

theorem lam_eq_zero_iff (j : σ) (y : Y) (hy : y ∈ C.U j) (F : MvPolynomial σ R) :
    C.lam j y hy F = 0 ↔ ∀ e, C.ev j y hy (homogeneousComponent e F) = 0 := by
  rw [lam_eq_sum]
  constructor
  · intro h e
    by_cases he : e ∈ Finset.range (F.totalDegree + 1)
    · have := congrArg (fun P => Polynomial.coeff P e) h
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at this
      rw [Finset.sum_eq_single e (fun b _ hb => by simp [Ne.symm hb])
        (fun h' => absurd he h')] at this
      simpa using this
    · rw [homogeneousComponent_eq_zero, map_zero]
      simp only [Finset.mem_range, not_lt] at he
      omega
  · intro h
    exact Finset.sum_eq_zero fun e _ => by rw [h e, map_zero, zero_mul]

/-- The homogeneous prime of a point `y`: the polynomials all of whose homogeneous components
vanish at `y`.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5. -/
def prime (y : Y) : Ideal (MvPolynomial σ R) :=
  RingHom.ker (C.lam (C.chart y) y (C.mem_chart y))

theorem mem_prime_iff (y : Y) (j : σ) (hj : y ∈ C.U j) (F : MvPolynomial σ R) :
    F ∈ C.prime y ↔ ∀ e, C.ev j y hj (homogeneousComponent e F) = 0 := by
  rw [prime, RingHom.mem_ker, lam_eq_zero_iff]
  exact forall_congr' fun e => C.ev_homog_eq_zero_iff j (C.chart y) y hj (C.mem_chart y) _ e
    (homogeneousComponent_isHomogeneous e F)

theorem mem_prime_iff_of_isHomogeneous (y : Y) (j : σ) (hj : y ∈ C.U j) (F : MvPolynomial σ R)
    (e : ℕ) (hF : F.IsHomogeneous e) : F ∈ C.prime y ↔ C.ev j y hj F = 0 := by
  rw [mem_prime_iff C y j hj]
  constructor
  · intro h
    have := h e
    simpa [homogeneousComponent_of_mem hF] using this
  · intro h e'
    rw [homogeneousComponent_of_mem hF]
    split_ifs
    · exact h
    · exact map_zero _

instance isPrime_prime (y : Y) : (C.prime y).IsPrime := RingHom.ker_isPrime _

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isHomogeneous_prime (y : Y) : (C.prime y).IsHomogeneous (homogeneousSubmodule σ R) := by
  intro i F hF
  rw [show ((DirectSum.decompose (homogeneousSubmodule σ R) F i : MvPolynomial σ R)) =
    homogeneousComponent i F from decomposition.decompose'_apply F i]
  rw [mem_prime_iff C y (C.chart y) (C.mem_chart y)] at hF ⊢
  intro e
  rw [homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous i F)]
  split_ifs with h
  · exact h ▸ hF i
  · exact map_zero _

theorem X_mem_prime_iff (y : Y) (j : σ) : X j ∈ C.prime y ↔ y ∉ C.U j := by
  rw [mem_prime_iff_of_isHomogeneous C y (C.chart y) (C.mem_chart y) (X j) 1 (isHomogeneous_X R j),
    ev_apply, Scheme.evaluation_eq_zero_iff_notMem_basicOpen, ← C.inter j (C.chart y)]
  simp [C.mem_chart y]

omit [Fintype σ] in
/-- Every section over a chart is the dehomogenization of a homogeneous polynomial. -/
theorem exists_isHomogeneous (j : σ) (s : Γ(Y, C.U j)) :
    ∃ (G : MvPolynomial σ R) (e : ℕ), G.IsHomogeneous e ∧ C.θ j G = s := by
  obtain ⟨F, rfl⟩ := C.θ_surj j s
  refine ⟨∑ e ∈ Finset.range (F.totalDegree + 1), X j ^ (F.totalDegree - e) *
    homogeneousComponent e F, F.totalDegree, ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun e he => ?_
    have he' : e ≤ F.totalDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 he)
    have := ((isHomogeneous_X R j).pow (F.totalDegree - e)).mul
      (homogeneousComponent_isHomogeneous e F)
    rwa [one_mul, Nat.sub_add_cancel he'] at this
  · rw [map_sum]
    conv_rhs => rw [← sum_homogeneousComponent F, map_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [map_mul, map_pow, C.θ_X_self, one_pow, one_mul]

theorem prime_mono {y y' : Y} (h : y ⤳ y') : C.prime y ≤ C.prime y' := by
  intro F hF
  obtain ⟨j, hj'⟩ := C.cover y'
  have hj : y ∈ C.U j := h.mem_open (C.U j).isOpen hj'
  rw [mem_prime_iff C y j hj] at hF
  rw [mem_prime_iff C y' j hj']
  intro e
  have := hF e
  rw [ev_apply, Scheme.evaluation_eq_zero_iff_notMem_basicOpen] at this ⊢
  exact fun h' => this (h.mem_open (Y.basicOpen _).isOpen h')

theorem specializes_of_prime_le {y y' : Y} (h : C.prime y ≤ C.prime y') : y ⤳ y' := by
  obtain ⟨j, hj'⟩ := C.cover y'
  have hj : y ∈ C.U j := by
    by_contra hn
    exact (C.X_mem_prime_iff y' j).1 (h ((C.X_mem_prime_iff y j).2 hn)) hj'
  have hU := C.affine j
  obtain ⟨p, rfl⟩ : y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hj
  obtain ⟨p', rfl⟩ : y' ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hj'
  refine Specializes.map ((PrimeSpectrum.le_iff_specializes p p').1 ?_) hU.fromSpec.continuous
  intro s hs
  obtain ⟨G, e, hG, rfl⟩ := C.exists_isHomogeneous j s
  have key : ∀ q : Spec Γ(Y, C.U j), C.θ j G ∈ q.asIdeal ↔ G ∈ C.prime (hU.fromSpec q) := by
    intro q
    have hq : hU.fromSpec q ∈ C.U j := by
      have : hU.fromSpec q ∈ Set.range hU.fromSpec := ⟨q, rfl⟩
      rwa [hU.range_fromSpec] at this
    have h2 : q ∈ (hU.fromSpec ⁻¹ᵁ Y.basicOpen (C.θ j G) : Set _) ↔ C.θ j G ∉ q.asIdeal := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact PrimeSpectrum.mem_basicOpen _ _
    rw [mem_prime_iff_of_isHomogeneous C _ j hq G e hG, ev_apply,
      Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
    change _ ↔ q ∉ (hU.fromSpec ⁻¹ᵁ Y.basicOpen (C.θ j G) : Set _)
    rw [h2, not_not]
  exact (key p').2 (h ((key p).1 hs))

theorem prime_le_iff {y y' : Y} : C.prime y ≤ C.prime y' ↔ y ⤳ y' :=
  ⟨C.specializes_of_prime_le, C.prime_mono⟩

theorem prime_injective : Function.Injective C.prime := fun _ _ h =>
  ((C.specializes_of_prime_le h.le).antisymm (C.specializes_of_prime_le h.ge)).eq

omit [Fintype σ] in
/-- At the point of a chart given by a prime `q`, a section vanishes exactly when it lies in
`q`. -/
theorem evaluation_fromSpec_eq_zero_iff (j : σ) (q : Spec Γ(Y, C.U j)) (hq : (C.affine j).fromSpec q ∈ C.U j)
    (s : Γ(Y, C.U j)) : Y.evaluation (C.U j) _ hq s = 0 ↔ s ∈ q.asIdeal := by
  have h2 : q ∈ ((C.affine j).fromSpec ⁻¹ᵁ Y.basicOpen s : Set _) ↔ s ∉ q.asIdeal := by
    rw [(C.affine j).fromSpec_preimage_basicOpen]
    exact PrimeSpectrum.mem_basicOpen _ _
  rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
  change q ∉ ((C.affine j).fromSpec ⁻¹ᵁ Y.basicOpen s : Set _) ↔ _
  rw [h2, not_not]

omit [Fintype σ] in
theorem fromSpec_mem (j : σ) (q : Spec Γ(Y, C.U j)) : (C.affine j).fromSpec q ∈ C.U j := by
  have : (C.affine j).fromSpec q ∈ Set.range (C.affine j).fromSpec := ⟨q, rfl⟩
  rwa [(C.affine j).range_fromSpec] at this

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- On an integral scheme every relevant homogeneous prime containing the homogeneous prime of
the generic point is the homogeneous prime of a point.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5(b). -/
theorem exists_prime_eq [IsIntegral Y] (P : Ideal (MvPolynomial σ R)) [P.IsPrime]
    (hhom : P.IsHomogeneous (homogeneousSubmodule σ R)) (j : σ) (hj : X j ∉ P)
    (hgen : C.prime (genericPoint Y) ≤ P) : ∃ y, C.prime y = P := by
  classical
  have hne : (C.U j : Set Y).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hj (hgen ((C.X_mem_prime_iff _ j).2 fun hm => by
      rw [← SetLike.mem_coe, h] at hm
      exact hm))
  have hη : genericPoint Y ∈ C.U j :=
    ((genericPoint_spec Y).mem_open_set_iff (C.U j).isOpen).2 (by simpa using hne)
  -- the kernel of the dehomogenization on homogeneous elements lies in `P`
  have hker : ∀ (G : MvPolynomial σ R) (e : ℕ), G.IsHomogeneous e → C.θ j G = 0 → G ∈ P := by
    intro G e hG h0
    refine hgen ((mem_prime_iff_of_isHomogeneous C _ j hη G e hG).2 ?_)
    rw [ev_apply, h0, map_zero]
  have hmem : ∀ (G : MvPolynomial σ R) (e : ℕ), G.IsHomogeneous e →
      ∀ (H : MvPolynomial σ R) (h : ℕ), H.IsHomogeneous h → H ∈ P → C.θ j G = C.θ j H →
        G ∈ P := by
    intro G e hG H h hH hHP heq
    have hK : (X j ^ h * G - X j ^ e * H).IsHomogeneous (h + e) := by
      refine IsHomogeneous.sub ?_ ?_
      · have := ((isHomogeneous_X R j).pow h).mul hG
        rwa [one_mul] at this
      · have := ((isHomogeneous_X R j).pow e).mul hH
        rwa [one_mul, add_comm] at this
    have h0 : C.θ j (X j ^ h * G - X j ^ e * H) = 0 := by
      rw [map_sub, map_mul, map_mul, map_pow, map_pow, C.θ_X_self, one_pow, one_pow, one_mul,
        one_mul, heq, sub_self]
    have := hker _ _ hK h0
    have h2 : X j ^ h * G ∈ P := by
      have := add_mem this (P.mul_mem_left (X j ^ e) hHP)
      rwa [sub_add_cancel] at this
    exact ((Ideal.IsPrime.mem_or_mem inferInstance h2).resolve_left
      fun h' => hj (Ideal.IsPrime.mem_of_pow_mem inferInstance h h'))
  -- the dehomogenized prime
  let p : Ideal Γ(Y, C.U j) :=
    { carrier := {s | ∃ (G : MvPolynomial σ R) (e : ℕ), G.IsHomogeneous e ∧ G ∈ P ∧ C.θ j G = s}
      add_mem' := by
        rintro _ _ ⟨G, e, hG, hGP, rfl⟩ ⟨H, h, hH, hHP, rfl⟩
        refine ⟨X j ^ h * G + X j ^ e * H, e + h, ?_, ?_, ?_⟩
        · refine IsHomogeneous.add ?_ ?_
          · have := ((isHomogeneous_X R j).pow h).mul hG
            rwa [one_mul, add_comm] at this
          · have := ((isHomogeneous_X R j).pow e).mul hH
            rwa [one_mul] at this
        · exact add_mem (P.mul_mem_left _ hGP) (P.mul_mem_left _ hHP)
        · rw [map_add, map_mul, map_mul, map_pow, map_pow, C.θ_X_self, one_pow, one_pow,
            one_mul, one_mul]
      zero_mem' := ⟨0, 0, isHomogeneous_zero _ _ _, zero_mem _, map_zero _⟩
      smul_mem' := by
        rintro c _ ⟨G, e, hG, hGP, rfl⟩
        obtain ⟨H, h, hH, rfl⟩ := C.exists_isHomogeneous j c
        exact ⟨H * G, h + e, hH.mul hG, P.mul_mem_left _ hGP, by rw [map_mul]; rfl⟩ }
  have hp_iff : ∀ (G : MvPolynomial σ R) (e : ℕ), G.IsHomogeneous e →
      (C.θ j G ∈ p ↔ G ∈ P) := by
    intro G e hG
    constructor
    · rintro ⟨H, h, hH, hHP, heq⟩
      exact hmem G e hG H h hH hHP heq.symm
    · intro hGP
      exact ⟨G, e, hG, hGP, rfl⟩
  have hp_prime : p.IsPrime := by
    refine ⟨fun htop => ?_, fun {s t} hst => ?_⟩
    · have h1 : (1 : Γ(Y, C.U j)) ∈ p := htop ▸ Submodule.mem_top
      rw [← C.θ_X_self j, hp_iff _ 1 (isHomogeneous_X R j)] at h1
      exact hj h1
    · obtain ⟨A, a, hA, rfl⟩ := C.exists_isHomogeneous j s
      obtain ⟨B, b, hB, rfl⟩ := C.exists_isHomogeneous j t
      rw [← map_mul, hp_iff _ _ (hA.mul hB)] at hst
      rcases Ideal.IsPrime.mem_or_mem inferInstance hst with h | h
      · exact Or.inl ((hp_iff A a hA).2 h)
      · exact Or.inr ((hp_iff B b hB).2 h)
  let q : Spec Γ(Y, C.U j) := ⟨p, hp_prime⟩
  refine ⟨(C.affine j).fromSpec q, ?_⟩
  ext F
  rw [mem_prime_iff C _ j (C.fromSpec_mem j q), mem_iff_homogeneousComponent_mem hhom]
  refine forall_congr' fun e => ?_
  rw [ev_apply, C.evaluation_fromSpec_eq_zero_iff j q]
  exact hp_iff _ e (homogeneousComponent_isHomogeneous e F)

end a3m_Charts

end HodgeLean.Adapters
