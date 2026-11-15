import HodgeLean.Adapters.IntersectionProductMovingFamily
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.GradedAlgebra.Radical

/-! # Homogeneity through the scaling action

An ideal of `R[x_σ]` (`R` a `ℂ`-algebra) that is stable under every scaling `x ↦ c x`, `c ≠ 0`,
is homogeneous: the homogeneous components of an element are linear combinations of its scalings
(Vandermonde). Minimal primes of homogeneous ideals are homogeneous.

Source: Bruns–Herzog, *Cohen–Macaulay Rings*, Lemma 1.5.6 (minimal primes of graded ideals);
the Vandermonde argument for torus actions over an infinite field. HC no distance; AV milestone
no distance.
-/

noncomputable section

open MvPolynomial

namespace HodgeLean.Adapters

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ R : Type} [CommRing R] [Algebra ℂ R]

/-- The scaling `x ↦ c x` of `R[x_σ]`. -/
def a3m_scale (c : ℂ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval fun k => MvPolynomial.C (algebraMap ℂ R c) * X k

theorem a3m_scale_of_isHomogeneous [Fintype σ] (c : ℂ) (G : MvPolynomial σ R) (e : ℕ)
    (hG : G.IsHomogeneous e) :
    a3m_scale c G = MvPolynomial.C (algebraMap ℂ R c) ^ e * G := by
  have h1 : ∀ H : MvPolynomial σ R, a3m_scale c H =
      eval₂ MvPolynomial.C (fun k => MvPolynomial.C (algebraMap ℂ R c) * X k) H := fun H => rfl
  rw [h1]
  conv_rhs => rw [← MvPolynomial.eval₂_eta G]
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = e := by
    rw [← hG (MvPolynomial.mem_support_iff.mp hm)]
    simp only [Finsupp.weight_apply, smul_eq_mul, Pi.one_apply, mul_one]
    exact (Finsupp.sum_fintype m (fun _ x ↦ x) (fun _ ↦ rfl)).symm
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hd]
  ring

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- An ideal stable under the scalings by nonzero complex numbers is homogeneous. -/
theorem a3m_isHomogeneous_of_scale [Fintype σ] (J : Ideal (MvPolynomial σ R))
    (hJ : ∀ c : ℂ, c ≠ 0 → ∀ G ∈ J, a3m_scale c G ∈ J) :
    J.IsHomogeneous (homogeneousSubmodule σ R) := by
  intro e G hG
  rw [show ((DirectSum.decompose (homogeneousSubmodule σ R) G e : MvPolynomial σ R)) =
    homogeneousComponent e G from decomposition.decompose'_apply G e]
  set N := G.totalDegree
  by_cases he : N < e
  · rw [homogeneousComponent_eq_zero _ _ he]; exact zero_mem _
  rw [not_lt] at he
  -- the scalings by `1, 2, …, N + 1`
  let v : Fin (N + 1) → ℂ := fun i => (i : ℂ) + 1
  have hv : Function.Injective v := by
    intro a b h
    simp only [v, add_left_inj, Nat.cast_inj] at h
    exact Fin.ext h
  have hv0 : ∀ i, v i ≠ 0 := fun i => by
    simp only [v]; exact_mod_cast Nat.succ_ne_zero i
  set V := Matrix.vandermonde v
  have hdet : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.2 hv
  have hsc : ∀ i, a3m_scale (v i) G = ∑ f : Fin (N + 1),
      MvPolynomial.C (algebraMap ℂ R (V i f)) * homogeneousComponent f G := by
    intro i
    conv_lhs => rw [← sum_homogeneousComponent G]
    rw [map_sum, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [a3m_scale_of_isHomogeneous _ _ f (homogeneousComponent_isHomogeneous f G)]
    simp [V, Matrix.vandermonde_apply]
  have hcomb : homogeneousComponent e G = ∑ i : Fin (N + 1),
      MvPolynomial.C (algebraMap ℂ R (V⁻¹ ⟨e, Nat.lt_succ_of_le he⟩ i)) * a3m_scale (v i) G := by
    simp_rw [hsc, Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← map_sum]
    have hinv : ∀ f : Fin (N + 1), ∑ i, V⁻¹ ⟨e, Nat.lt_succ_of_le he⟩ i * V i f =
        if f = ⟨e, Nat.lt_succ_of_le he⟩ then 1 else 0 := by
      intro f
      have h1 := Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.2 hdet)
      have h2 := congrArg (fun A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ =>
        A ⟨e, Nat.lt_succ_of_le he⟩ f) h1
      simp only [Matrix.mul_apply, Matrix.one_apply] at h2
      rw [h2]
      exact if_congr eq_comm rfl rfl
    simp_rw [hinv]
    simp
  rw [hcomb]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hJ _ (hv0 i) G hG)

omit [Algebra ℂ R] in
attribute [local instance] MvPolynomial.gradedAlgebra in
/-- Minimal primes of a homogeneous ideal are homogeneous.
Source: Bruns–Herzog, *Cohen–Macaulay Rings*, Lemma 1.5.6. -/
theorem a3m_isHomogeneous_of_mem_minimalPrimes {J Q : Ideal (MvPolynomial σ R)}
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ R)) (hQ : Q ∈ J.minimalPrimes) :
    Q.IsHomogeneous (homogeneousSubmodule σ R) := by
  have hcore : (Q.homogeneousCore (homogeneousSubmodule σ R)).toIdeal.IsPrime := hQ.1.1.homogeneousCore
  have hle : J ≤ (Q.homogeneousCore (homogeneousSubmodule σ R)).toIdeal :=
    hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hQ.1.2)
  have h := hQ.2 ⟨hcore, hle⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
  rw [le_antisymm h (Ideal.toIdeal_homogeneousCore_le _ _)]
  exact (Q.homogeneousCore (homogeneousSubmodule σ R)).isHomogeneous

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- A homogeneous ideal is stable under the scalings. -/
theorem a3m_scale_mem_of_isHomogeneous [Fintype σ] {I : Ideal (MvPolynomial σ R)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R)) (c : ℂ) {F : MvPolynomial σ R}
    (hF : F ∈ I) : a3m_scale c F ∈ I := by
  rw [← sum_homogeneousComponent F, map_sum]
  refine Ideal.sum_mem _ fun e _ => ?_
  rw [a3m_scale_of_isHomogeneous _ _ e (homogeneousComponent_isHomogeneous e F)]
  exact Ideal.mul_mem_left _ _ (homogeneousComponent_mem_of_mem hI hF e)

theorem a3m_scale_C (c : ℂ) (r : R) : a3m_scale (σ := σ) c (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.aeval_C _ _

theorem a3m_scale_X (c : ℂ) (k : σ) :
    a3m_scale (σ := σ) (R := R) c (X k) = MvPolynomial.C (algebraMap ℂ R c) * X k :=
  MvPolynomial.aeval_X _ _

section FamilyScale

variable [Fintype σ] [DecidableEq σ] (I_C : Ideal (MvPolynomial σ ℂ)) [I_C.IsPrime]
  (hIC : I_C.IsHomogeneous (homogeneousSubmodule σ ℂ)) (M : Matrix σ σ ℂ) (c : ℂ)

/-- The scaling on `B₀/I_C`. -/
def a3m_scaleA : (MvPolynomial σ ℂ ⧸ I_C) →+* (MvPolynomial σ ℂ ⧸ I_C) :=
  Ideal.quotientMap I_C (a3m_scale (R := ℂ) c).toRingHom
    (fun _ hF => a3m_scale_mem_of_isHomogeneous hIC c hF)

theorem a3m_scaleA_algebraMap (x : ℂ) :
    a3m_scaleA I_C hIC c (algebraMap ℂ _ x) = algebraMap ℂ _ x := by
  change Ideal.Quotient.mk I_C (a3m_scale c (MvPolynomial.C x)) = _
  rw [a3m_scale_C]
  rfl

theorem a3m_map_scaleA_algebraMap (h : Polynomial ℂ) :
    Polynomial.map (a3m_scaleA I_C hIC c) (h.map (algebraMap ℂ (MvPolynomial σ ℂ ⧸ I_C))) =
      h.map (algebraMap ℂ (MvPolynomial σ ℂ ⧸ I_C)) := by
  rw [Polynomial.map_map]
  congr 1
  ext x
  exact a3m_scaleA_algebraMap I_C hIC c x

/-- The scaling on `(B₀/I_C)[t][1/det h_t]`. -/
def a3m_scaleD : a3m_D I_C M →+* a3m_D I_C M :=
  Localization.awayLift ((a3m_ιD I_C M).comp (Polynomial.mapRingHom (a3m_scaleA I_C hIC c)))
    (a3m_detA I_C M) (by
      have hmap : Polynomial.map (a3m_scaleA I_C hIC c) (a3m_detA I_C M) = a3m_detA I_C M :=
        a3m_map_scaleA_algebraMap I_C hIC c (a3m_det M)
      rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, hmap]
      exact IsLocalization.Away.algebraMap_isUnit _)

theorem a3m_scaleD_ι (p : Polynomial (MvPolynomial σ ℂ ⧸ I_C)) :
    a3m_scaleD I_C hIC M c (a3m_ιD I_C M p) =
      a3m_ιD I_C M (p.map (a3m_scaleA I_C hIC c)) := by
  rw [a3m_scaleD]
  exact IsLocalization.Away.lift_eq _ _ p

theorem a3m_scaleD_invSelf :
    a3m_scaleD I_C hIC M c (IsLocalization.Away.invSelf (a3m_detA I_C M)) =
      IsLocalization.Away.invSelf (a3m_detA I_C M) := by
  have hmap : Polynomial.map (a3m_scaleA I_C hIC c) (a3m_detA I_C M) = a3m_detA I_C M :=
    a3m_map_scaleA_algebraMap I_C hIC c (a3m_det M)
  have h1 := congrArg (a3m_scaleD I_C hIC M c)
    (IsLocalization.Away.mul_invSelf (S := a3m_D I_C M) (a3m_detA I_C M))
  rw [map_mul, map_one] at h1
  change a3m_scaleD I_C hIC M c (a3m_ιD I_C M (a3m_detA I_C M)) * _ = 1 at h1
  rw [a3m_scaleD_ι, hmap] at h1
  have h2 := IsLocalization.Away.mul_invSelf (S := a3m_D I_C M) (a3m_detA I_C M)
  have hu : IsUnit (a3m_ιD I_C M (a3m_detA I_C M)) := IsLocalization.Away.algebraMap_isUnit _
  exact hu.mul_left_cancel (h1.trans h2.symm)

theorem a3m_scaleD_algebraMap (x : ℂ) :
    a3m_scaleD I_C hIC M c (algebraMap ℂ (a3m_D I_C M) x) = algebraMap ℂ (a3m_D I_C M) x := by
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial (MvPolynomial σ ℂ ⧸ I_C)) (a3m_D I_C M),
    show algebraMap (Polynomial (MvPolynomial σ ℂ ⧸ I_C)) (a3m_D I_C M) = a3m_ιD I_C M from rfl,
    a3m_scaleD_ι, Polynomial.algebraMap_apply, Polynomial.map_C, a3m_scaleA_algebraMap]

theorem a3m_famHom₀_scale :
    (a3m_famHom₀ I_C M).comp (a3m_scale (R := ℂ) c).toRingHom =
      (a3m_scaleD I_C hIC M c).comp (a3m_famHom₀ I_C M) := by
  refine MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, a3m_scale_C]
    simp only [a3m_famHom₀, coe_eval₂Hom, eval₂_C]
    rw [a3m_scaleD_algebraMap]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, a3m_scale_X]
    simp only [a3m_famHom₀, coe_eval₂Hom, eval₂_C, eval₂_X, map_mul, map_sum,
      a3m_scaleD_ι, a3m_scaleD_invSelf]
    have hx : ∀ l, Polynomial.map (a3m_scaleA I_C hIC c)
        (Polynomial.C (Ideal.Quotient.mk I_C (X l))) =
        Polynomial.C (algebraMap ℂ (MvPolynomial σ ℂ ⧸ I_C) c) *
          Polynomial.C (Ideal.Quotient.mk I_C (X l)) := by
      intro l
      rw [Polynomial.map_C, ← Polynomial.C_mul]
      congr 1
      change Ideal.Quotient.mk I_C (a3m_scale c (X l)) = _
      rw [a3m_scale_X, map_mul]
      rfl
    simp only [hx, a3m_map_scaleA_algebraMap, map_mul]
    have hz : a3m_ιD I_C M (Polynomial.C (algebraMap ℂ (MvPolynomial σ ℂ ⧸ I_C) c)) =
        algebraMap ℂ (a3m_D I_C M) c := by
      rw [IsScalarTower.algebraMap_apply ℂ (Polynomial (MvPolynomial σ ℂ ⧸ I_C)) (a3m_D I_C M),
        Polynomial.algebraMap_apply]
    rw [hz, Algebra.algebraMap_self, RingHom.id_apply]
    simp_rw [mul_left_comm _ (algebraMap ℂ (a3m_D I_C M) c), ← Finset.mul_sum]
    ring

theorem a3m_famHom_scale :
    (a3m_famHom I_C M).comp (Polynomial.mapRingHom (a3m_scale (R := ℂ) c).toRingHom) =
      (a3m_scaleD I_C hIC M c).comp (a3m_famHom I_C M) := by
  refine Polynomial.ringHom_ext (fun F => ?_) ?_
  · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, a3m_famHom,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    exact congrArg (fun φ : MvPolynomial σ ℂ →+* a3m_D I_C M => φ F) (a3m_famHom₀_scale I_C hIC M c)
  · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, a3m_famHom,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, a3m_scaleD_ι]

include hIC in
theorem a3m_famIdeal_scale {G : Polynomial (MvPolynomial σ ℂ)} (hG : G ∈ a3m_famIdeal I_C M) :
    Polynomial.map (a3m_scale (R := ℂ) c).toRingHom G ∈ a3m_famIdeal I_C M := by
  rw [a3m_famIdeal, RingHom.mem_ker] at hG ⊢
  have := congrArg (fun φ : Polynomial (MvPolynomial σ ℂ) →+* a3m_D I_C M => φ G)
    (a3m_famHom_scale I_C hIC M c)
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom] at this
  rw [this, hG, map_zero]

end FamilyScale

/-- Minimal primes are transported by ring isomorphisms. -/
theorem a3m_map_mem_minimalPrimes {A B : Type} [CommRing A] [CommRing B] (f : A ≃+* B)
    {J Q : Ideal A} (hQ : Q ∈ J.minimalPrimes) : Q.map f ∈ (J.map f).minimalPrimes := by
  have hQp : Q.IsPrime := hQ.1.1
  rw [← Ideal.comap_symm, ← Ideal.comap_symm]
  refine ⟨⟨Ideal.comap_isPrime _ _, Ideal.comap_mono hQ.1.2⟩, fun Q' hQ' hle => ?_⟩
  obtain ⟨hQ'p, hJQ'⟩ := hQ'
  have h1 : J ≤ Q'.comap f := fun x hx => by
    have := hJQ' (show f.symm (f x) ∈ J by simpa using hx)
    simpa using this
  have h2 : Q'.comap f ≤ Q := fun x hx => by
    have := hle (show f x ∈ Q' from hx)
    simpa using this
  have h3 := hQ.2 ⟨Ideal.comap_isPrime _ _, h1⟩ h2
  intro x hx
  have := h3 (show f.symm x ∈ Q from hx)
  rw [Ideal.mem_comap, RingEquiv.apply_symm_apply] at this
  exact this

section Transport

variable (σ) [Fintype σ] [DecidableEq σ]

/-- `B₀[t] ≃ ℂ[t][x]`. -/
def a3m_eq : Polynomial (MvPolynomial σ ℂ) ≃ₐ[ℂ] MvPolynomial σ (Polynomial ℂ) :=
  (MvPolynomial.optionEquivLeft ℂ σ).symm.trans (MvPolynomial.optionEquivRight ℂ σ)

theorem a3m_eq_C (F : MvPolynomial σ ℂ) :
    a3m_eq σ (Polynomial.C F) = MvPolynomial.map Polynomial.C F := by
  have : (a3m_eq σ).toRingHom.comp Polynomial.C = MvPolynomial.map Polynomial.C := by
    refine MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)
    · simp [a3m_eq, MvPolynomial.optionEquivLeft_symm_C_C, MvPolynomial.optionEquivRight_C]
    · simp [a3m_eq, MvPolynomial.optionEquivLeft_symm_C_X, MvPolynomial.optionEquivRight_X_some]
  exact congrArg (fun φ : MvPolynomial σ ℂ →+* _ => φ F) this

theorem a3m_eq_X : a3m_eq σ Polynomial.X = MvPolynomial.C Polynomial.X := by
  simp [a3m_eq, MvPolynomial.optionEquivLeft_symm_X, MvPolynomial.optionEquivRight_X_none]

theorem a3m_eq_scale (c : ℂ) (G : Polynomial (MvPolynomial σ ℂ)) :
    a3m_eq σ (Polynomial.map (a3m_scale (R := ℂ) c).toRingHom G) =
      a3m_scale (R := Polynomial ℂ) c (a3m_eq σ G) := by
  have hmapC : (MvPolynomial.map Polynomial.C).comp (a3m_scale (σ := σ) (R := ℂ) c).toRingHom =
      (a3m_scale (R := Polynomial ℂ) c).toRingHom.comp (MvPolynomial.map Polynomial.C) := by
    refine MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)
    · simp [a3m_scale_C]
    · simp [a3m_scale_X, Polynomial.algebraMap_apply]
  have : (a3m_eq σ).toRingHom.comp (Polynomial.mapRingHom (a3m_scale (R := ℂ) c).toRingHom) =
      (a3m_scale (R := Polynomial ℂ) c).toRingHom.comp (a3m_eq σ).toRingHom := by
    refine Polynomial.ringHom_ext (fun F => ?_) ?_
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
      change a3m_eq σ _ = a3m_scale c (a3m_eq σ _)
      rw [a3m_eq_C, a3m_eq_C]
      exact congrArg (fun φ : MvPolynomial σ ℂ →+* _ => φ F) hmapC
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
      change a3m_eq σ _ = a3m_scale c (a3m_eq σ _)
      rw [a3m_eq_X, a3m_scale_C]
  exact congrArg (fun φ : Polynomial (MvPolynomial σ ℂ) →+* _ => φ G) this

variable {σ}

/-- The family ideal, moved to `ℂ[t][x]`, is homogeneous in `x`. -/
theorem a3m_famInter_isHomogeneous (I_X I_C : Ideal (MvPolynomial σ ℂ)) [I_X.IsPrime] [I_C.IsPrime]
    (hIX : I_X.IsHomogeneous (homogeneousSubmodule σ ℂ))
    (hIC : I_C.IsHomogeneous (homogeneousSubmodule σ ℂ)) (M : Matrix σ σ ℂ) :
    (Ideal.map (a3m_eq σ) (a3m_famInter I_X I_C M)).IsHomogeneous
      (homogeneousSubmodule σ (Polynomial ℂ)) := by
  refine a3m_isHomogeneous_of_scale _ fun c _ G hG => ?_
  have hstab : a3m_famInter I_X I_C M ≤ (a3m_famInter I_X I_C M).comap
      (Polynomial.mapRingHom (a3m_scale (R := ℂ) c).toRingHom) := by
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun F hF => ?_) fun G hG => ?_
    · rw [Ideal.mem_comap, Ideal.mem_comap, Polynomial.coe_mapRingHom, Polynomial.map_C]
      exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (a3m_scale_mem_of_isHomogeneous hIX c hF))
    · exact Ideal.mem_sup_right (a3m_famIdeal_scale I_C hIC M c hG)
  obtain ⟨H, hH, rfl⟩ := (Ideal.mem_map_of_equiv (a3m_eq σ).toRingEquiv G).1 hG
  change a3m_scale c (a3m_eq σ H) ∈ _
  rw [← a3m_eq_scale]
  exact Ideal.mem_map_of_mem _ (hstab hH)

end Transport

end HodgeLean.Adapters
