import HodgeLean.Adapters.IntersectionProductMovingCoords
import HodgeLean.Adapters.IntersectionProductMovingFamily
import HodgeLean.Adapters.CyclePushforwardDimension

/-! # Points of a scheme with projective `Spec`-charts as homogeneous primes

A variant of `a3m_Charts` in which the charts are open immersions `κ j : Spec (T j) ⟶ Y` and the
dehomogenizations `θ j : R[x_σ] → T j` are surjective ring maps with `θ j (x_j) = 1`; on overlaps
the chart `l` meets the chart `j` exactly where `θ l (x_j)` does not vanish, and a homogeneous
polynomial vanishes at a point in one chart exactly when it vanishes there in the other. Each
point `y` then has the relevant homogeneous prime `a3m_SpecCharts.prime y`, specialization is
inclusion of primes, and on an integral `Y` every relevant homogeneous prime containing the prime
of the generic point is the prime of a point.

Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5; Stacks Project, Tag 00JP.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

namespace HodgeLean.Adapters

/-- Projective `Spec`-charts on a scheme `Y`.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5. -/
structure a3m_SpecCharts (Y : Scheme.{0}) (σ : Type) (R : Type) [CommRing R] where
  /-- The chart rings. -/
  T : σ → CommRingCat.{0}
  /-- The charts. -/
  κ : ∀ j, Spec (T j) ⟶ Y
  [isOpenImmersion : ∀ j, IsOpenImmersion (κ j)]
  cover : ∀ y : Y, ∃ j, y ∈ Set.range (κ j)
  /-- The dehomogenizations. -/
  θ : ∀ j, MvPolynomial σ R →+* T j
  θ_X_self : ∀ j, θ j (X j) = 1
  θ_surj : ∀ j, Function.Surjective (θ j)
  inter : ∀ (j l : σ) (p : Spec (T l)), κ l p ∈ Set.range (κ j) ↔ θ l (X j) ∉ p.asIdeal
  compat : ∀ (j l : σ) (p : Spec (T j)) (p' : Spec (T l)), κ j p = κ l p' →
    ∀ (F : MvPolynomial σ R) (e : ℕ), F.IsHomogeneous e → (θ j F ∈ p.asIdeal ↔ θ l F ∈ p'.asIdeal)

attribute [instance] a3m_SpecCharts.isOpenImmersion

namespace a3m_SpecCharts

variable {Y : Scheme.{0}} {σ : Type} {R : Type} [CommRing R] (C : a3m_SpecCharts Y σ R)

/-- A chart containing `y`. -/
def chart (y : Y) : σ := (C.cover y).choose

theorem mem_chart (y : Y) : y ∈ Set.range (C.κ (C.chart y)) := (C.cover y).choose_spec

/-- The point of the chart over `y`. -/
def pt (y : Y) : Spec (C.T (C.chart y)) := (C.mem_chart y).choose

theorem κ_pt (y : Y) : C.κ (C.chart y) (C.pt y) = y := (C.mem_chart y).choose_spec

variable [Fintype σ]

/-- The graded value at a prime `p` of the chart `j`: `F ↦ Σ_e (θ_j F_e mod p) λ^e`. -/
def lam (j : σ) (p : Spec (C.T j)) : MvPolynomial σ R →+* Polynomial (C.T j ⧸ p.asIdeal) :=
  eval₂Hom (Polynomial.C.comp ((Ideal.Quotient.mk _).comp ((C.θ j).comp MvPolynomial.C)))
    (fun k => Polynomial.C (Ideal.Quotient.mk _ (C.θ j (X k))) * Polynomial.X)

theorem lam_of_isHomogeneous (j : σ) (p : Spec (C.T j)) (F : MvPolynomial σ R) (e : ℕ)
    (hF : F.IsHomogeneous e) :
    C.lam j p F = Polynomial.C (Ideal.Quotient.mk _ (C.θ j F)) * Polynomial.X ^ e := by
  rw [lam, coe_eval₂Hom, a3m_Charts.a3m_eval₂_mul_X_of_isHomogeneous _ _ F e hF]
  congr 2
  have h1 := MvPolynomial.eval₂_comp_left (C.θ j) MvPolynomial.C X F
  rw [MvPolynomial.eval₂_eta] at h1
  have h2 := MvPolynomial.eval₂_comp_left (Ideal.Quotient.mk p.asIdeal)
    ((C.θ j).comp MvPolynomial.C) (fun k => C.θ j (X k)) F
  rw [h1]
  exact h2.symm

theorem lam_eq_zero_iff (j : σ) (p : Spec (C.T j)) (F : MvPolynomial σ R) :
    C.lam j p F = 0 ↔ ∀ e, C.θ j (homogeneousComponent e F) ∈ p.asIdeal := by
  have hsum : C.lam j p F = ∑ e ∈ Finset.range (F.totalDegree + 1),
      Polynomial.C (Ideal.Quotient.mk _ (C.θ j (homogeneousComponent e F))) * Polynomial.X ^ e := by
    conv_lhs => rw [← sum_homogeneousComponent F]
    rw [map_sum]
    exact Finset.sum_congr rfl fun e _ =>
      C.lam_of_isHomogeneous j p _ e (homogeneousComponent_isHomogeneous e F)
  rw [hsum]
  constructor
  · intro h e
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    by_cases he : e ∈ Finset.range (F.totalDegree + 1)
    · have := congrArg (fun P => Polynomial.coeff P e) h
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at this
      rw [Finset.sum_eq_single e (fun b _ hb => by simp [Ne.symm hb])
        (fun h' => absurd he h')] at this
      simpa using this
    · rw [homogeneousComponent_eq_zero, map_zero, map_zero]
      simp only [Finset.mem_range, not_lt] at he
      omega
  · intro h
    exact Finset.sum_eq_zero fun e _ => by
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (h e), Polynomial.C_0, zero_mul]

omit [Fintype σ] in
theorem mem_iff_of_isHomogeneous_of_eq (j l : σ) (p : Spec (C.T j)) (p' : Spec (C.T l))
    (h : C.κ j p = C.κ l p') (F : MvPolynomial σ R) :
    (∀ e, C.θ j (homogeneousComponent e F) ∈ p.asIdeal) ↔
      ∀ e, C.θ l (homogeneousComponent e F) ∈ p'.asIdeal :=
  forall_congr' fun e => C.compat j l p p' h _ e (homogeneousComponent_isHomogeneous e F)

/-- The homogeneous prime of a point `y`: the polynomials all of whose homogeneous components
vanish at `y`.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5. -/
def prime (y : Y) : Ideal (MvPolynomial σ R) := RingHom.ker (C.lam (C.chart y) (C.pt y))

theorem mem_prime_iff (y : Y) (j : σ) (p : Spec (C.T j)) (hp : C.κ j p = y)
    (F : MvPolynomial σ R) : F ∈ C.prime y ↔ ∀ e, C.θ j (homogeneousComponent e F) ∈ p.asIdeal := by
  rw [prime, RingHom.mem_ker, lam_eq_zero_iff]
  exact C.mem_iff_of_isHomogeneous_of_eq _ _ _ _ ((C.κ_pt y).trans hp.symm) F

theorem mem_prime_iff_of_isHomogeneous (y : Y) (j : σ) (p : Spec (C.T j)) (hp : C.κ j p = y)
    (F : MvPolynomial σ R) (e : ℕ) (hF : F.IsHomogeneous e) :
    F ∈ C.prime y ↔ C.θ j F ∈ p.asIdeal := by
  rw [mem_prime_iff C y j p hp]
  constructor
  · intro h
    simpa [homogeneousComponent_of_mem hF] using h e
  · intro h e'
    rw [homogeneousComponent_of_mem hF]
    split_ifs
    · exact h
    · rw [map_zero]; exact zero_mem _

instance isPrime_prime (y : Y) : (C.prime y).IsPrime := by
  have : (C.pt y).asIdeal.IsPrime := (C.pt y).isPrime
  have : IsDomain (C.T (C.chart y) ⧸ (C.pt y).asIdeal) := Ideal.Quotient.isDomain _
  exact RingHom.ker_isPrime _

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isHomogeneous_prime (y : Y) : (C.prime y).IsHomogeneous (homogeneousSubmodule σ R) := by
  intro i F hF
  rw [show ((DirectSum.decompose (homogeneousSubmodule σ R) F i : MvPolynomial σ R)) =
    homogeneousComponent i F from decomposition.decompose'_apply F i]
  rw [mem_prime_iff C y _ _ (C.κ_pt y)] at hF ⊢
  intro e
  rw [homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous i F)]
  split_ifs with h
  · exact h ▸ hF i
  · rw [map_zero]; exact zero_mem _

theorem X_mem_prime_iff (y : Y) (j : σ) : X j ∈ C.prime y ↔ y ∉ Set.range (C.κ j) := by
  rw [mem_prime_iff_of_isHomogeneous C y _ _ (C.κ_pt y) (X j) 1 (isHomogeneous_X R j)]
  have := C.inter j (C.chart y) (C.pt y)
  rw [C.κ_pt y] at this
  tauto

omit [Fintype σ] in
/-- Every element of a chart ring is the dehomogenization of a homogeneous polynomial. -/
theorem exists_isHomogeneous (j : σ) (s : C.T j) :
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
  obtain ⟨j, p', hp'⟩ := C.cover y'
  have hy : y ∈ Set.range (C.κ j) :=
    h.mem_open (C.κ j).isOpenEmbedding.isOpen_range (hp' ▸ ⟨p', rfl⟩)
  obtain ⟨p, hp⟩ := hy
  rw [mem_prime_iff C y j p hp] at hF
  rw [mem_prime_iff C y' j p' hp']
  have hpp' : p ⤳ p' := by
    rw [← (C.κ j).isOpenEmbedding.isInducing.specializes_iff, hp, hp']
    exact h
  intro e
  exact (PrimeSpectrum.le_iff_specializes p p').2 hpp' (hF e)

theorem specializes_of_prime_le {y y' : Y} (h : C.prime y ≤ C.prime y') : y ⤳ y' := by
  obtain ⟨j, p', hp'⟩ := C.cover y'
  have hy : y ∈ Set.range (C.κ j) := by
    by_contra hn
    have := h ((C.X_mem_prime_iff y j).2 hn)
    exact (C.X_mem_prime_iff y' j).1 this (hp' ▸ ⟨p', rfl⟩)
  obtain ⟨p, hp⟩ := hy
  rw [← hp, ← hp']
  refine Specializes.map ((PrimeSpectrum.le_iff_specializes p p').1 ?_) (C.κ j).continuous
  intro s hs
  obtain ⟨G, e, hG, rfl⟩ := C.exists_isHomogeneous j s
  rw [← mem_prime_iff_of_isHomogeneous C y j p hp G e hG] at hs
  exact (mem_prime_iff_of_isHomogeneous C y' j p' hp' G e hG).1 (h hs)

theorem prime_le_iff {y y' : Y} : C.prime y ≤ C.prime y' ↔ y ⤳ y' :=
  ⟨C.specializes_of_prime_le, C.prime_mono⟩

theorem prime_injective : Function.Injective C.prime := fun _ _ h =>
  ((C.specializes_of_prime_le h.le).antisymm (C.specializes_of_prime_le h.ge)).eq

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- On an integral scheme every relevant homogeneous prime containing the homogeneous prime of
the generic point is the homogeneous prime of a point.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5(b). -/
theorem exists_prime_eq [IsIntegral Y] (P : Ideal (MvPolynomial σ R)) [P.IsPrime]
    (hhom : P.IsHomogeneous (homogeneousSubmodule σ R)) (j : σ) (hj : X j ∉ P)
    (hgen : C.prime (genericPoint Y) ≤ P) : ∃ y, C.prime y = P := by
  classical
  have hη : genericPoint Y ∈ Set.range (C.κ j) := by
    by_contra h
    exact hj (hgen ((C.X_mem_prime_iff _ j).2 h))
  obtain ⟨p₀, hp₀⟩ := hη
  have hker : ∀ (G : MvPolynomial σ R) (e : ℕ), G.IsHomogeneous e → C.θ j G = 0 → G ∈ P := by
    intro G e hG h0
    refine hgen ((mem_prime_iff_of_isHomogeneous C _ j p₀ hp₀ G e hG).2 ?_)
    rw [h0]; exact zero_mem _
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
  let p : Ideal (C.T j) :=
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
    · have h1 : (1 : C.T j) ∈ p := htop ▸ Submodule.mem_top
      rw [← C.θ_X_self j, hp_iff _ 1 (isHomogeneous_X R j)] at h1
      exact hj h1
    · obtain ⟨A, a, hA, rfl⟩ := C.exists_isHomogeneous j s
      obtain ⟨B, b, hB, rfl⟩ := C.exists_isHomogeneous j t
      rw [← map_mul, hp_iff _ _ (hA.mul hB)] at hst
      rcases Ideal.IsPrime.mem_or_mem inferInstance hst with h | h
      · exact Or.inl ((hp_iff A a hA).2 h)
      · exact Or.inr ((hp_iff B b hB).2 h)
  let q : Spec (C.T j) := ⟨p, hp_prime⟩
  refine ⟨C.κ j q, ?_⟩
  ext F
  rw [mem_prime_iff C _ j q rfl, mem_iff_homogeneousComponent_mem hhom]
  exact forall_congr' fun e => hp_iff _ e (homogeneousComponent_isHomogeneous e F)

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- A relevant homogeneous prime containing the homogeneous polynomials that vanish on a chart is
the homogeneous prime of a point.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5(b). -/
theorem exists_prime_eq' (P : Ideal (MvPolynomial σ R)) [P.IsPrime]
    (hhom : P.IsHomogeneous (homogeneousSubmodule σ R)) (j : σ) (hj : X j ∉ P)
    (hker : ∀ (G : MvPolynomial σ R) (e : ℕ), G.IsHomogeneous e → C.θ j G = 0 → G ∈ P) :
    ∃ y, C.prime y = P := by
  classical
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
  let p : Ideal (C.T j) :=
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
    · have h1 : (1 : C.T j) ∈ p := htop ▸ Submodule.mem_top
      rw [← C.θ_X_self j, hp_iff _ 1 (isHomogeneous_X R j)] at h1
      exact hj h1
    · obtain ⟨A, a, hA, rfl⟩ := C.exists_isHomogeneous j s
      obtain ⟨B, b, hB, rfl⟩ := C.exists_isHomogeneous j t
      rw [← map_mul, hp_iff _ _ (hA.mul hB)] at hst
      rcases Ideal.IsPrime.mem_or_mem inferInstance hst with h | h
      · exact Or.inl ((hp_iff A a hA).2 h)
      · exact Or.inr ((hp_iff B b hB).2 h)
  let q : Spec (C.T j) := ⟨p, hp_prime⟩
  refine ⟨C.κ j q, ?_⟩
  ext F
  rw [mem_prime_iff C _ j q rfl, mem_iff_homogeneousComponent_mem hhom]
  exact forall_congr' fun e => hp_iff _ e (homogeneousComponent_isHomogeneous e F)

end a3m_SpecCharts

/-- An open immersion from an affine scheme into a scheme locally of finite type over `ℂ`
preserves heights (both are the transcendence degree of the residue field).
Source: Hartshorne, *Algebraic Geometry*, Exercise II.3.20. -/
theorem a3m_height_openImmersion {Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType Y.hom]
    {T : CommRingCat.{0}} (κ : Spec T ⟶ Y.left) [IsOpenImmersion κ] (p : Spec T) :
    Order.height (κ p) = Order.height p := by
  set U := κ.opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange κ
  have hrange : Set.range κ = Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]; rfl
  let e := IsOpenImmersion.isoOfRangeEq κ hU.fromSpec hrange
  have he : e.hom ≫ hU.fromSpec = κ := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hq : hU.fromSpec (e.hom p) = κ p := by rw [← Scheme.Hom.comp_apply, he]
  obtain ⟨-, n, hn, htr⟩ := a1d_height_chart (X := Y) (κ p) U hU (e.hom p) hq
  obtain ⟨-, m, hm, htr'⟩ := a1d_height_eq_trdeg (X := Y) (κ p)
  have hnm : n = m := by exact_mod_cast htr.symm.trans htr'
  let h := Scheme.homeoOfIso e
  let o : Spec T ≃o Spec Γ(Y.left, U) :=
    { toEquiv := h.toEquiv
      map_rel_iff' := fun {a b} => by
        change h a ≤ h b ↔ a ≤ b
        rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
        exact h.isInducing.specializes_iff }
  have hqp : Order.height (e.hom p) = Order.height p := Order.height_orderIso o p
  rw [hm, ← hnm, ← hn, hqp]

theorem a3m_SpecCharts.lam_algebraMap {Y : Scheme.{0}} {σ R : Type} [Fintype σ] [CommRing R]
    [Algebra ℂ R] (C : a3m_SpecCharts Y σ R) [∀ j, Algebra ℂ (C.T j)]
    (hθ : ∀ j (c : ℂ), C.θ j (algebraMap ℂ _ c) = algebraMap ℂ _ c) (j : σ)
    (p : Spec (C.T j)) (c : ℂ) :
    C.lam j p (algebraMap ℂ _ c) = algebraMap ℂ (Polynomial (C.T j ⧸ p.asIdeal)) c := by
  rw [MvPolynomial.algebraMap_apply]
  simp only [a3m_SpecCharts.lam, coe_eval₂Hom, eval₂_C, RingHom.coe_comp, Function.comp_apply]
  rw [← MvPolynomial.algebraMap_apply, hθ j c, Polynomial.algebraMap_apply]
  rfl

theorem a3m_SpecCharts.lam_X_self {Y : Scheme.{0}} {σ R : Type} [Fintype σ] [CommRing R]
    (C : a3m_SpecCharts Y σ R) (j : σ) (p : Spec (C.T j)) :
    C.lam j p (X j) = Polynomial.X := by
  simp [a3m_SpecCharts.lam, C.θ_X_self]

/-- The height formula for a point of a scheme over `ℂ` with projective charts: the affine cone
over `closure {y}` has dimension `dim closure {y} + 1`.
Source: Hartshorne, *Algebraic Geometry*, I, Exercise 2.6 and II, Exercise 3.20. -/
theorem a3m_SpecCharts.height_add_one {Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType Y.hom]
    {σ R : Type} [Fintype σ] [CommRing R] [Algebra ℂ R] [Algebra.FiniteType ℂ R]
    (C : a3m_SpecCharts Y.left σ R) [∀ j, Algebra ℂ (C.T j)]
    (hθ : ∀ j (c : ℂ), C.θ j (algebraMap ℂ _ c) = algebraMap ℂ _ c) (y : Y.left) :
    (Order.height y : WithBot ℕ∞) + 1 = ringKrullDim (MvPolynomial σ R ⧸ C.prime y) := by
  set j := C.chart y
  set p := C.pt y
  have hp : p.asIdeal.IsPrime := p.isPrime
  have h1 : (Order.height y : WithBot ℕ∞) = ringKrullDim (C.T j ⧸ p.asIdeal) := by
    have h := a3m_height_openImmersion (C.κ j) p
    rw [C.κ_pt y] at h
    rw [h]
    exact hc9k8_height_spec (C.T j) p
  let θa : MvPolynomial σ R →ₐ[ℂ] C.T j := { C.θ j with commutes' := hθ j }
  have : Algebra.FiniteType ℂ (C.T j) := Algebra.FiniteType.of_surjective θa (C.θ_surj j)
  have : Algebra.FiniteType ℂ (C.T j ⧸ p.asIdeal) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  let lamA : MvPolynomial σ R →ₐ[ℂ] Polynomial (C.T j ⧸ p.asIdeal) :=
    { C.lam j p with
      commutes' := C.lam_algebraMap hθ j p }
  have h2 := a3m_ringKrullDim_cone lamA (X j) (C.lam_X_self j p) (fun s => by
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective s
      obtain ⟨G, e, hG, rfl⟩ := C.exists_isHomogeneous j t
      exact ⟨G, e, C.lam_of_isHomogeneous j p G e hG⟩)
  rw [h1, ← h2]
  rfl

/-- A global section of `Spec T`, pulled back to `Z`, vanishes at `z` exactly when it lies in the
prime of the image of `z`. -/
theorem a3m_Γevaluation_spec_eq_zero_iff {T : CommRingCat.{0}} (q : Spec T) (s : T) :
    (Spec T).Γevaluation q ((Scheme.ΓSpecIso T).inv s) = 0 ↔ s ∈ q.asIdeal := by
  have h2 : q ∈ ((Spec T).basicOpen ((Scheme.ΓSpecIso T).inv s) : Set (Spec T)) ↔
      s ∉ q.asIdeal := by
    rw [basicOpen_eq_of_affine]
    exact PrimeSpectrum.mem_basicOpen _ _
  exact (Scheme.evaluation_eq_zero_iff_notMem_basicOpen _ _ _ _).trans
    ((not_congr h2).trans not_not)

theorem a3m_Γevaluation_appTop_eq_zero_iff {Z : Scheme.{0}} {T : CommRingCat.{0}}
    (f : Z ⟶ Spec T) (z : Z) (s : T) :
    Z.Γevaluation z (f.appTop ((Scheme.ΓSpecIso T).inv s)) = 0 ↔ s ∈ (f z).asIdeal := by
  rw [← Scheme.Γevaluation_naturality_apply, map_eq_zero_iff _ (f.residueFieldMap z).hom.injective]
  exact a3m_Γevaluation_spec_eq_zero_iff (f z) s

/-- The overlap criterion for chart compatibility: if on each overlap `Spec T_j ×_Y Spec T_l` a
homogeneous `F` of degree `e` satisfies `θ_l F = (θ_l x_j)^e · θ_j F`, then a homogeneous
polynomial vanishes at a point in one chart exactly when it vanishes there in the other. -/
theorem a3m_compat_of_overlap {Y : Scheme.{0}} {σ R : Type} [CommRing R] {T : σ → CommRingCat.{0}}
    (κ : ∀ j, Spec (T j) ⟶ Y) (θ : ∀ j, MvPolynomial σ R →+* T j)
    (inter : ∀ (j l : σ) (p : Spec (T l)), κ l p ∈ Set.range (κ j) ↔ θ l (X j) ∉ p.asIdeal)
    (hov : ∀ (j l : σ) (F : MvPolynomial σ R) (e : ℕ), F.IsHomogeneous e →
      (pullback.snd (κ j) (κ l)).appTop ((Scheme.ΓSpecIso _).inv (θ l F)) =
        (pullback.snd (κ j) (κ l)).appTop ((Scheme.ΓSpecIso _).inv (θ l (X j))) ^ e *
          (pullback.fst (κ j) (κ l)).appTop ((Scheme.ΓSpecIso _).inv (θ j F)))
    (j l : σ) (p : Spec (T j)) (p' : Spec (T l)) (h : κ j p = κ l p')
    (F : MvPolynomial σ R) (e : ℕ) (hF : F.IsHomogeneous e) :
    θ j F ∈ p.asIdeal ↔ θ l F ∈ p'.asIdeal := by
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback p p' h
  have hX : θ l (X j) ∉ p'.asIdeal := (inter j l p').1 (h ▸ ⟨p, rfl⟩)
  have key := congrArg ((pullback (κ j) (κ l)).Γevaluation z) (hov j l F e hF)
  rw [map_mul, map_pow] at key
  rw [← hz1, ← hz2, ← a3m_Γevaluation_appTop_eq_zero_iff, ← a3m_Γevaluation_appTop_eq_zero_iff,
    key]
  have hX' : (pullback (κ j) (κ l)).Γevaluation z
      ((pullback.snd (κ j) (κ l)).appTop ((Scheme.ΓSpecIso _).inv (θ l (X j)))) ≠ 0 := by
    rw [Ne, a3m_Γevaluation_appTop_eq_zero_iff, hz2]
    exact hX
  rw [mul_eq_zero, or_iff_right (pow_ne_zero _ hX')]

/-- Projective charts on an open subscheme `U ⊆ Y` from charts of `Y` covering `U`. -/
def a3m_SpecCharts.ofOpen {Y : Scheme.{0}} {σ R : Type} [CommRing R] (U : Y.Opens)
    (T : σ → CommRingCat.{0}) (κ : ∀ j, Spec (T j) ⟶ Y) [∀ j, IsOpenImmersion (κ j)]
    (hU : ∀ j, Set.range (κ j) ⊆ U) (hcov : ∀ y ∈ U, ∃ j, y ∈ Set.range (κ j))
    (θ : ∀ j, MvPolynomial σ R →+* T j) (θ_X_self : ∀ j, θ j (X j) = 1)
    (θ_surj : ∀ j, Function.Surjective (θ j))
    (inter : ∀ (j l : σ) (p : Spec (T l)), κ l p ∈ Set.range (κ j) ↔ θ l (X j) ∉ p.asIdeal)
    (compat : ∀ (j l : σ) (p : Spec (T j)) (p' : Spec (T l)), κ j p = κ l p' →
      ∀ (F : MvPolynomial σ R) (e : ℕ), F.IsHomogeneous e →
        (θ j F ∈ p.asIdeal ↔ θ l F ∈ p'.asIdeal)) :
    a3m_SpecCharts U.toScheme σ R where
  T := T
  κ j := IsOpenImmersion.lift U.ι (κ j) (by rw [Scheme.Opens.range_ι]; exact hU j)
  isOpenImmersion j := by
    have : IsOpenImmersion (IsOpenImmersion.lift U.ι (κ j)
        (by rw [Scheme.Opens.range_ι]; exact hU j) ≫ U.ι) := by
      rw [IsOpenImmersion.lift_fac]; infer_instance
    exact IsOpenImmersion.of_comp _ U.ι
  cover y := by
    obtain ⟨j, p, hp⟩ := hcov (U.ι y) y.2
    refine ⟨j, p, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac, hp]
  θ := θ
  θ_X_self := θ_X_self
  θ_surj := θ_surj
  inter j l p := by
    rw [← inter j l p]
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨q, ?_⟩
      have := congrArg U.ι hq
      rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac,
        IsOpenImmersion.lift_fac] at this
    · rintro ⟨q, hq⟩
      refine ⟨q, U.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac,
        IsOpenImmersion.lift_fac, hq]
  compat j l p p' h := by
    refine compat j l p p' ?_
    have := congrArg U.ι h
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac] at this

theorem a3m_SpecCharts.ofOpen_κ {Y : Scheme.{0}} {σ R : Type} [CommRing R] (U : Y.Opens)
    (T : σ → CommRingCat.{0}) (κ : ∀ j, Spec (T j) ⟶ Y) [∀ j, IsOpenImmersion (κ j)]
    (hU : ∀ j, Set.range (κ j) ⊆ U) (hcov : ∀ y ∈ U, ∃ j, y ∈ Set.range (κ j))
    (θ : ∀ j, MvPolynomial σ R →+* T j) (θ_X_self) (θ_surj) (inter) (compat) (j : σ) :
    (a3m_SpecCharts.ofOpen U T κ hU hcov θ θ_X_self θ_surj inter compat).κ j ≫ U.ι = κ j :=
  IsOpenImmersion.lift_fac _ _ _

end HodgeLean.Adapters
