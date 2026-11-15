import HodgeLean.Adapters.IntersectionProductBlochRobertsPoints
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
/-! # Passing from cone separation to projective coordinate rigidity

These algebraic lemmas compare homogeneous cone maps with maps of affine chart
rings and their fraction fields.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Order MvPolynomial TensorProduct
namespace HodgeLean.Adapters
local instance (A : Type*) : DecidableEq A := Classical.decEq A

/-- Separation of homogeneous cone maps also separates proportional chart coordinates. -/
theorem IntersectionProductScaf_cone_separation_dehomogenizes
    {ρ σ B E : Type} [Fintype ρ] [Fintype σ] [CommRing B] [Algebra ℂ B]
    [Field E] [Algebra ℂ E]
    (θ : MvPolynomial (σ ⊕ Unit) ℂ →ₐ[ℂ] B) (hθ : Function.Surjective θ)
    (j : σ) (hj : θ (MvPolynomial.X (Sum.inl j)) = 1)
    (lam : MvPolynomial (σ ⊕ Unit) ℂ →ₐ[ℂ] Polynomial B)
    (hleft : ∀ k, lam (MvPolynomial.X (Sum.inl k)) =
      Polynomial.C (θ (MvPolynomial.X (Sum.inl k))) * Polynomial.X)
    (hright : lam (MvPolynomial.X (Sum.inr ())) =
      Polynomial.C (θ (MvPolynomial.X (Sum.inr ()))))
    (a : ρ × σ → ℂ)
    (hsep : ∀ (K : Type) [Field K] [Algebra ℂ K]
      (φ ψ : (MvPolynomial (σ ⊕ Unit) ℂ ⧸ RingHom.ker lam.toRingHom) →ₐ[ℂ] K),
      Function.Injective φ →
      (∀ i, φ (Ideal.Quotient.mk _ (a3r_lin (a3h_block a) (MvPolynomial.X i))) =
        ψ (Ideal.Quotient.mk _ (a3r_lin (a3h_block a) (MvPolynomial.X i)))) → φ = ψ)
    (f g : B →ₐ[ℂ] E) (hf : Function.Injective f) (z : E)
    (hproj : ∀ i : ρ, f (θ (a3r_lin (a3h_block a) (MvPolynomial.X (Sum.inl i)))) =
      z * g (θ (a3r_lin (a3h_block a) (MvPolynomial.X (Sum.inl i)))))
    (ht : f (θ (MvPolynomial.X (Sum.inr ()))) = g (θ (MvPolynomial.X (Sum.inr ())))) :
    f = g ∧ z = 1 := by
  let P := RingHom.ker lam.toRingHom
  let F := (Polynomial.mapAlgHom f).comp lam
  let G := (Polynomial.eval₂AlgHom ((Polynomial.CAlgHom : E →ₐ[ℂ] Polynomial E).comp g)
    (Polynomial.C z * Polynomial.X) (fun _ => Commute.all _ _)).comp lam
  let Fq : (MvPolynomial (σ ⊕ Unit) ℂ ⧸ P) →ₐ[ℂ] Polynomial E :=
    Ideal.Quotient.liftₐ P F (by
      intro x hx
      change lam x = 0 at hx
      simp [F, hx])
  let Gq : (MvPolynomial (σ ⊕ Unit) ℂ ⧸ P) →ₐ[ℂ] Polynomial E :=
    Ideal.Quotient.liftₐ P G (by
      intro x hx
      change lam x = 0 at hx
      simp [G, hx])
  have hF : Function.Injective Fq := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change lam p = 0
    apply Polynomial.map_injective f.toRingHom hf
    change Polynomial.map f.toRingHom (lam p) = Polynomial.map f.toRingHom 0
    change Polynomial.map f.toRingHom (lam p) = 0 at hx
    simpa only [Polynomial.map_zero] using hx
  let K := FractionRing (Polynomial E)
  let ι : Polynomial E →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ (Polynomial E) K
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial E) K
  have hFX (k : σ) : F (MvPolynomial.X (Sum.inl k)) =
      Polynomial.C (f (θ (MvPolynomial.X (Sum.inl k)))) * Polynomial.X := by
    simp [F, hleft]
  have hGX (k : σ) : G (MvPolynomial.X (Sum.inl k)) =
      Polynomial.C (g (θ (MvPolynomial.X (Sum.inl k)))) *
        (Polynomial.C z * Polynomial.X) := by
    simp [G, hleft]
  have hlin (i : ρ ⊕ Unit) : F (a3r_lin (a3h_block a) (MvPolynomial.X i)) =
      G (a3r_lin (a3h_block a) (MvPolynomial.X i)) := by
    cases i with
    | inl i =>
      have hFl : F (a3r_lin (a3h_block a) (MvPolynomial.X (Sum.inl i))) =
          Polynomial.C (f (θ (a3r_lin (a3h_block a) (MvPolynomial.X (Sum.inl i))))) *
            Polynomial.X := by
        simp only [a3h_lin_block_inl, map_sum, map_mul, hFX,
          ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply,
          Finset.sum_mul, mul_assoc]
      have hGl : G (a3r_lin (a3h_block a) (MvPolynomial.X (Sum.inl i))) =
          Polynomial.C (g (θ (a3r_lin (a3h_block a) (MvPolynomial.X (Sum.inl i))))) *
            (Polynomial.C z * Polynomial.X) := by
        simp only [a3h_lin_block_inl, map_sum, map_mul, hGX,
          ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply,
          Finset.sum_mul, mul_assoc]
      rw [hFl, hGl, hproj, map_mul]
      ring
    | inr u =>
      cases u
      simpa [F, G, a3h_lin_block_inr, hright] using congrArg Polynomial.C ht
  have he := hsep K (ι.comp Fq) (ι.comp Gq) (hι.comp hF) (fun i => by
    change ι (F (a3r_lin (a3h_block a) (MvPolynomial.X i))) =
      ι (G (a3r_lin (a3h_block a) (MvPolynomial.X i)))
    rw [hlin])
  have he' (p : MvPolynomial (σ ⊕ Unit) ℂ) : F p = G p := by
    apply hι
    exact congrArg (fun q : (MvPolynomial (σ ⊕ Unit) ℂ ⧸ P) →ₐ[ℂ] K =>
      q (Ideal.Quotient.mk P p)) he
  have hz : z = 1 := by
    have h := congrArg (fun p : Polynomial E => p.coeff 1)
      (he' (MvPolynomial.X (Sum.inl j)))
    simpa [F, G, hleft, hj] using h.symm
  refine ⟨?_, hz⟩
  apply (AlgHom.cancel_right hθ).mp
  apply MvPolynomial.algHom_ext
  intro k
  cases k with
  | inl k =>
    have h := congrArg (fun p : Polynomial E => p.coeff 1)
      (he' (MvPolynomial.X (Sum.inl k)))
    simpa [F, G, hleft, hz] using h
  | inr u =>
    cases u
    exact ht
#print axioms IntersectionProductScaf_cone_separation_dehomogenizes
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rigidity for proportional affine coordinates determines the degree over their projective ratios. -/
theorem IntersectionProductScaf_finrank_one_of_ratio_rigidity
    {ι : Type} (B K L : Type) [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra ℂ B] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] [Algebra B L] [IsScalarTower ℂ B L] [IsFractionRing B L]
    [Module.Finite K L] [CharZero K]
    (u : ι → B) (v t : B) (hv : v ≠ 0)
    (hu : ∀ i, ∃ k : K, algebraMap K L k = algebraMap B L (u i) / algebraMap B L v)
    (ht : ∃ k : K, algebraMap K L k = algebraMap B L t)
    (hrig : ∀ (E : Type) [Field E] [Algebra ℂ E] (f g : B →ₐ[ℂ] E),
      Function.Injective f → ∀ z : E,
      (∀ i, f (u i) = z * g (u i)) → f t = g t → f = g) :
    Module.finrank K L = 1 := by
  let E := AlgebraicClosure L
  have hvL : algebraMap B L v ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B L).ne hv
  haveI : Subsingleton (L →ₐ[K] E) := ⟨by
    intro φ ψ
    let f := (φ.restrictScalars ℂ).comp (IsScalarTower.toAlgHom ℂ B L)
    let g := (ψ.restrictScalars ℂ).comp (IsScalarTower.toAlgHom ℂ B L)
    have he := hrig E f g (φ.injective.comp (IsFractionRing.injective B L))
      (φ (algebraMap B L v) / ψ (algebraMap B L v)) (fun i => by
        obtain ⟨k, hk⟩ := hu i
        have h : φ (algebraMap B L (u i)) / φ (algebraMap B L v) =
            ψ (algebraMap B L (u i)) / ψ (algebraMap B L v) := by
          rw [← map_div₀ φ, ← map_div₀ ψ, ← hk, φ.commutes, ψ.commutes]
        have hφv : φ (algebraMap B L v) ≠ 0 := by
          exact (map_ne_zero φ).mpr hvL
        have hψv : ψ (algebraMap B L v) ≠ 0 := by
          exact (map_ne_zero ψ).mpr hvL
        change φ (algebraMap B L (u i)) =
          φ (algebraMap B L v) / ψ (algebraMap B L v) * ψ (algebraMap B L (u i))
        have hh := (div_eq_div_iff hφv hψv).mp h
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hψv).mpr
        simpa only [mul_comm] using hh) (by
          obtain ⟨k, hk⟩ := ht
          change φ (algebraMap B L t) = ψ (algebraMap B L t)
          rw [← hk, φ.commutes, ψ.commutes])
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors B)
    ext b
    exact congrArg (fun q : B →ₐ[ℂ] E => q b) he⟩
  haveI : Nonempty (L →ₐ[K] E) := ⟨IsScalarTower.toAlgHom K L E⟩
  rw [← AlgHom.card K L E]
  exact Fintype.card_eq_one_iff.mpr ⟨IsScalarTower.toAlgHom K L E, fun _ => Subsingleton.elim _ _⟩
#print axioms IntersectionProductScaf_finrank_one_of_ratio_rigidity


attribute [local instance] MvPolynomial.gradedAlgebra in
/-- The relative cone prime is the kernel of homogenized evaluation in any chart containing the point. -/
theorem IntersectionProductScaf_relative_cone_chart_kernel
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (y : (a3n_T X).left) (hy : y ∈ a3h_U X)
    (j : Fin (a3s_N X + 1)) (p : Spec ((a3s_LC X).T j))
    (hp : (a3s_LC X).κ j p = a3h_pt X y hy) :
    a3h_P X y hy = RingHom.ker (((a3s_LC X).lam j p).comp
      ((a3m_eq (Fin (a3s_N X + 1))).toRingHom.comp
        (a3h_eqT (Fin (a3s_N X + 1))).toRingHom)) := by
  ext F
  change (a3m_eq _) (a3h_eqT _ F) ∈ (a3s_LC X).prime (a3h_pt X y hy) ↔
    (a3s_LC X).lam j p ((a3m_eq _) (a3h_eqT _ F)) = 0
  rw [(a3s_LC X).mem_prime_iff _ j p hp, (a3s_LC X).lam_eq_zero_iff]
#print axioms IntersectionProductScaf_relative_cone_chart_kernel


/-- Homogeneous separation determines maps out of the actual quotient of a relative chart ring. -/
theorem IntersectionProductScaf_relative_chart_map_rigidity
    {Y : Scheme.{0}} {ρ σ : Type} [Fintype ρ] [Fintype σ]
    (C : a3m_SpecCharts Y σ (Polynomial ℂ)) [∀ j, Algebra ℂ (C.T j)]
    (hθ : ∀ j (c : ℂ), C.θ j (algebraMap ℂ _ c) = algebraMap ℂ _ c)
    (y : Y) (j : σ) (p : Spec (C.T j)) (hp : C.κ j p = y)
    (a : ρ × σ → ℂ)
    (hsep : ∀ (K : Type) [Field K] [Algebra ℂ K]
      (φ ψ : (MvPolynomial (σ ⊕ Unit) ℂ ⧸ (C.prime y).comap
        ((a3m_eq σ).toRingHom.comp (a3h_eqT σ).toRingHom)) →ₐ[ℂ] K),
      Function.Injective φ →
      (∀ i, φ (Ideal.Quotient.mk _ (a3r_lin (a3h_block a) (MvPolynomial.X i))) =
        ψ (Ideal.Quotient.mk _ (a3r_lin (a3h_block a) (MvPolynomial.X i)))) → φ = ψ)
    (E : Type) [Field E] [Algebra ℂ E]
    (f g : (C.T j ⧸ p.asIdeal) →ₐ[ℂ] E) (hf : Function.Injective f) (z : E)
    (hproj : ∀ i : ρ,
      f (Ideal.Quotient.mk p.asIdeal (C.θ j ((a3m_eq σ) ((a3h_eqT σ)
        (a3r_lin (a3h_block a) (MvPolynomial.X (Sum.inl i))))))) =
      z * g (Ideal.Quotient.mk p.asIdeal (C.θ j ((a3m_eq σ) ((a3h_eqT σ)
        (a3r_lin (a3h_block a) (MvPolynomial.X (Sum.inl i))))))))
    (ht : f (Ideal.Quotient.mk p.asIdeal (C.θ j (MvPolynomial.C Polynomial.X))) =
      g (Ideal.Quotient.mk p.asIdeal (C.θ j (MvPolynomial.C Polynomial.X)))) :
    f = g ∧ z = 1 := by
  let e := (a3m_eq σ).toAlgHom.comp (a3h_eqT σ).toAlgHom
  let θ₀ : MvPolynomial σ (Polynomial ℂ) →ₐ[ℂ] C.T j :=
    { C.θ j with commutes' := hθ j }
  let θ := (Ideal.Quotient.mkₐ ℂ p.asIdeal).comp (θ₀.comp e)
  let lam₀ : MvPolynomial σ (Polynomial ℂ) →ₐ[ℂ] Polynomial (C.T j ⧸ p.asIdeal) :=
    { C.lam j p with commutes' := C.lam_algebraMap hθ j p }
  let lam := lam₀.comp e
  have heleft (k : σ) : e (MvPolynomial.X (Sum.inl k)) = MvPolynomial.X k := by
    simp [e, a3h_eqT_inl, a3m_eq_C]
  have heright : e (MvPolynomial.X (Sum.inr ())) = MvPolynomial.C Polynomial.X := by
    simp [e, a3h_eqT_inr, a3m_eq_X]
  have hker : (C.prime y).comap e.toRingHom = RingHom.ker lam.toRingHom := by
    ext F
    change e F ∈ C.prime y ↔ C.lam j p (e F) = 0
    rw [C.mem_prime_iff y j p hp, C.lam_eq_zero_iff]
  change ∀ (K : Type) [Field K] [Algebra ℂ K]
      (φ ψ : (MvPolynomial (σ ⊕ Unit) ℂ ⧸ (C.prime y).comap e.toRingHom) →ₐ[ℂ] K),
      Function.Injective φ →
      (∀ i, φ (Ideal.Quotient.mk _ (a3r_lin (a3h_block a) (MvPolynomial.X i))) =
        ψ (Ideal.Quotient.mk _ (a3r_lin (a3h_block a) (MvPolynomial.X i)))) → φ = ψ at hsep
  rw [hker] at hsep
  apply IntersectionProductScaf_cone_separation_dehomogenizes θ
    ((Ideal.Quotient.mkₐ_surjective ℂ p.asIdeal).comp ((C.θ_surj j).comp
      ((a3m_eq σ).surjective.comp (a3h_eqT σ).surjective))) j ?_ lam ?_ ?_ a hsep f g hf z hproj ?_
  · change Ideal.Quotient.mk p.asIdeal (C.θ j (e (MvPolynomial.X (Sum.inl j)))) = 1
    rw [heleft, C.θ_X_self, map_one]
  · intro k
    change C.lam j p (e (MvPolynomial.X (Sum.inl k))) =
      Polynomial.C (Ideal.Quotient.mk p.asIdeal (C.θ j (e (MvPolynomial.X (Sum.inl k))))) * Polynomial.X
    rw [heleft, C.lam_of_isHomogeneous j p _ 1 (isHomogeneous_X _ _), pow_one]
  · change C.lam j p (e (MvPolynomial.X (Sum.inr ()))) =
      Polynomial.C (Ideal.Quotient.mk p.asIdeal (C.θ j (e (MvPolynomial.X (Sum.inr ())))))
    rw [heright, C.lam_of_isHomogeneous j p _ 0 (isHomogeneous_C _ _), pow_zero, mul_one]
  · change f (Ideal.Quotient.mk p.asIdeal (C.θ j (e (MvPolynomial.X (Sum.inr ()))))) =
      g (Ideal.Quotient.mk p.asIdeal (C.θ j (e (MvPolynomial.X (Sum.inr ())))))
    rwa [heright]
#print axioms IntersectionProductScaf_relative_chart_map_rigidity

section PointConeSeparation
open CategoryTheory.Limits HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Ring.toIntAlgebra AddCommGroup.toIntModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- General projections have no off-diagonal pair of the input dimension. -/
theorem IntersectionProductScaf_generic_absolute_diagonal
    {ρ σ : Type} [Fintype ρ] [Fintype σ]
    (P : Ideal (MvPolynomial σ ℂ)) [P.IsPrime]
    (d : ℕ) (hd : ringKrullDim (MvPolynomial σ ℂ ⧸ P) = d)
    (hdim : d < Fintype.card ρ) :
    a3r_Generic {a : ρ × σ → ℂ |
      ∀ Q : Ideal ((MvPolynomial σ ℂ ⧸ P) ⊗[ℂ]
        (MvPolynomial σ ℂ ⧸ P)), Q.IsPrime →
      (d : WithBot ℕ∞) ≤ ringKrullDim (_ ⧸ Q) →
      (∀ i, ∑ k, algebraMap ℂ _ (a3r_mat a i k) * a3r_δD P P k - 0 ∈ Q) →
      ∀ j, a3r_δD P P j ∈ Q} := by
  let A := MvPolynomial σ ℂ ⧸ P
  have : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) (Ideal.Quotient.mkₐ_surjective ℂ P)
  refine (a3r_generic_secant (ρ := ρ) P P).mono ?_
  intro a ha Q hQ hQdim hrel j
  by_contra hj
  have hb := ha j Q hQ hj hrel
  rw [hc9k8_ringKrullDim_tensorProduct, hd] at hb
  have hc : (d : WithBot ℕ∞) + (Fintype.card ρ : ℕ) ≤ (d : WithBot ℕ∞) + d :=
    (add_le_add hQdim le_rfl).trans hb
  have hn : d + Fintype.card ρ ≤ d + d := by exact_mod_cast hc
  omega
#print axioms IntersectionProductScaf_generic_absolute_diagonal

/-- Projections separate injective maps of a sufficiently small cone into a field. -/
theorem IntersectionProductScaf_generic_absolute_separates_maps
    {ρ σ : Type} [Fintype ρ] [Fintype σ]
    (P : Ideal (MvPolynomial σ ℂ)) [P.IsPrime]
    (d : ℕ) (hd : ringKrullDim (MvPolynomial σ ℂ ⧸ P) = d)
    (hdim : d < Fintype.card ρ) :
    a3r_Generic {a : ρ × σ → ℂ |
      ∀ (K : Type) [Field K] [Algebra ℂ K]
        (φ ψ : (MvPolynomial σ ℂ ⧸ P) →ₐ[ℂ] K),
        Function.Injective φ →
        (∀ i, φ (Ideal.Quotient.mk P (a3r_lin (a3r_mat a) (MvPolynomial.X i))) =
          ψ (Ideal.Quotient.mk P (a3r_lin (a3r_mat a) (MvPolynomial.X i)))) → φ = ψ} := by
  classical
  let A := MvPolynomial σ ℂ ⧸ P
  have : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) (Ideal.Quotient.mkₐ_surjective ℂ P)
  refine (IntersectionProductScaf_generic_absolute_diagonal P d hd hdim).mono ?_
  intro a ha K _ _ φ ψ hφ hrel
  let Θ : A ⊗[ℂ] A →ₐ[ℂ] K := Algebra.TensorProduct.productMap φ ψ
  let Q := RingHom.ker Θ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime _
  let ι : A →ₐ[ℂ] (A ⊗[ℂ] A) ⧸ Q :=
    (Ideal.Quotient.mkₐ ℂ Q).comp Algebra.TensorProduct.includeLeft
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply hφ
    rw [map_zero]
    have hh : (x ⊗ₜ[ℂ] (1 : A)) ∈ Q :=
      Ideal.Quotient.eq_zero_iff_mem.mp hx
    simpa only [Q, RingHom.mem_ker, Θ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.productMap_apply_tmul,
      map_one, mul_one] using hh
  have hQdim : (d : WithBot ℕ∞) ≤ ringKrullDim ((A ⊗[ℂ] A) ⧸ Q) := by
    rw [← hd]
    exact a3m_ringKrullDim_le_of_injective ι hι
  have hlinear (i : ρ) :
      ∑ k, algebraMap ℂ (A ⊗[ℂ] A) (a3r_mat a i k) * a3r_δD P P k - 0 ∈ Q := by
    change Θ _ = 0
    have h := hrel i
    simp only [a3r_lin_X, map_sum, map_mul, ← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap, AlgHom.commutes] at h
    simp only [Θ, map_sub, map_sum, map_mul, AlgHom.commutes, map_zero, sub_zero,
      a3r_δD, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, one_mul,
      mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  have he := ha Q inferInstance hQdim hlinear
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  have hj := he j
  change Θ (a3r_δD P P j) = 0 at hj
  change φ (Ideal.Quotient.mk P (MvPolynomial.X j)) = ψ (Ideal.Quotient.mk P (MvPolynomial.X j))
  simpa only [Θ, a3r_δD, map_sub, Algebra.TensorProduct.productMap_apply_tmul,
    map_one, mul_one, one_mul, sub_eq_zero] using hj
#print axioms IntersectionProductScaf_generic_absolute_separates_maps

/-- General relative projections have no off-diagonal pair of the input dimension. -/
theorem IntersectionProductScaf_generic_small_relative_diagonal
    {ρ σ : Type} [Fintype ρ] [Fintype σ]
    (P : Ideal (MvPolynomial (σ ⊕ Unit) ℂ)) [P.IsPrime]
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (σ ⊕ Unit) ℂ ⧸ P) = d)
    (hdim : d < Fintype.card ρ) :
    a3r_Generic {a : ρ × σ → ℂ |
      ∀ Q : Ideal ((MvPolynomial (σ ⊕ Unit) ℂ ⧸ P) ⊗[ℂ]
        (MvPolynomial (σ ⊕ Unit) ℂ ⧸ P)), Q.IsPrime →
      (d : WithBot ℕ∞) ≤ ringKrullDim (_ ⧸ Q) →
      (∀ i, ∑ k, algebraMap ℂ _ (a3h_block a i k) * a3r_δD P P k - 0 ∈ Q) →
      ∀ j, a3r_δD P P j ∈ Q} := by
  let A := MvPolynomial (σ ⊕ Unit) ℂ ⧸ P
  have : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) (Ideal.Quotient.mkₐ_surjective ℂ P)
  let D := A ⊗[ℂ] A
  have : Algebra.FiniteType ℂ D := a3r_finiteType_tensor (A := A) (B := A)
  refine (a3r_generic_iInter_fintype _ fun j : σ =>
    a3r_generic_linear (ρ := ρ) D (fun k => a3r_δD P P (Sum.inl k)) 0 j).mono ?_
  intro a ha Q hQ hQdim hrel j
  cases j with
  | inl j =>
    by_contra hj
    have hb := ha j Q hQ hj (fun i => by
      have h := hrel (Sum.inl i)
      simpa only [Fintype.sum_sum_type, a3h_block_inl_inl, a3h_block_inl_inr,
        a3h_block_inr_inl, a3h_block_inr_inr, a3r_mat, map_zero, map_one, Pi.zero_apply,
        Fintype.sum_unique, zero_mul, add_zero] using h)
    rw [hc9k8_ringKrullDim_tensorProduct, hd] at hb
    have hc : (d : WithBot ℕ∞) + (Fintype.card ρ : ℕ) ≤ (d : WithBot ℕ∞) + d :=
      (add_le_add hQdim le_rfl).trans hb
    have hn : d + Fintype.card ρ ≤ d + d := by exact_mod_cast hc
    omega
  | inr j =>
    cases j
    have h := hrel (Sum.inr ())
    simpa only [Fintype.sum_sum_type, a3h_block_inl_inl, a3h_block_inl_inr,
        a3h_block_inr_inl, a3h_block_inr_inr, a3r_mat, map_zero, map_one, Pi.zero_apply,
      Fintype.sum_unique, zero_mul, Finset.sum_const_zero, zero_add, one_mul, sub_zero]
      using h
#print axioms IntersectionProductScaf_generic_small_relative_diagonal

/-- Relative projections separate injective maps of a sufficiently small cone into a field. -/
theorem IntersectionProductScaf_generic_small_relative_separates_maps
    {ρ σ : Type} [Fintype ρ] [Fintype σ]
    (P : Ideal (MvPolynomial (σ ⊕ Unit) ℂ)) [P.IsPrime]
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (σ ⊕ Unit) ℂ ⧸ P) = d)
    (hdim : d < Fintype.card ρ) :
    a3r_Generic {a : ρ × σ → ℂ |
      ∀ (K : Type) [Field K] [Algebra ℂ K]
        (φ ψ : (MvPolynomial (σ ⊕ Unit) ℂ ⧸ P) →ₐ[ℂ] K),
        Function.Injective φ →
        (∀ i, φ (Ideal.Quotient.mk P (a3r_lin (a3h_block a) (MvPolynomial.X i))) =
          ψ (Ideal.Quotient.mk P (a3r_lin (a3h_block a) (MvPolynomial.X i)))) → φ = ψ} := by
  classical
  let A := MvPolynomial (σ ⊕ Unit) ℂ ⧸ P
  have : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) (Ideal.Quotient.mkₐ_surjective ℂ P)
  refine (IntersectionProductScaf_generic_small_relative_diagonal P d hd hdim).mono ?_
  intro a ha K _ _ φ ψ hφ hrel
  let Θ : A ⊗[ℂ] A →ₐ[ℂ] K := Algebra.TensorProduct.productMap φ ψ
  let Q := RingHom.ker Θ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime _
  let ι : A →ₐ[ℂ] (A ⊗[ℂ] A) ⧸ Q :=
    (Ideal.Quotient.mkₐ ℂ Q).comp Algebra.TensorProduct.includeLeft
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply hφ
    rw [map_zero]
    have hh : (x ⊗ₜ[ℂ] (1 : A)) ∈ Q :=
      Ideal.Quotient.eq_zero_iff_mem.mp hx
    simpa only [Q, RingHom.mem_ker, Θ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.productMap_apply_tmul,
      map_one, mul_one] using hh
  have hQdim : (d : WithBot ℕ∞) ≤ ringKrullDim ((A ⊗[ℂ] A) ⧸ Q) := by
    rw [← hd]
    exact a3m_ringKrullDim_le_of_injective ι hι
  have hlinear (i : ρ ⊕ Unit) :
      ∑ k, algebraMap ℂ (A ⊗[ℂ] A) (a3h_block a i k) * a3r_δD P P k - 0 ∈ Q := by
    change Θ _ = 0
    have h := hrel i
    simp only [a3r_lin_X, map_sum, map_mul, ← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap, AlgHom.commutes] at h
    simp only [Θ, map_sub, map_sum, map_mul, AlgHom.commutes, map_zero, sub_zero,
      a3r_δD, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, one_mul,
      mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  have he := ha Q inferInstance hQdim hlinear
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  have hj := he j
  change Θ (a3r_δD P P j) = 0 at hj
  change φ (Ideal.Quotient.mk P (MvPolynomial.X j)) = ψ (Ideal.Quotient.mk P (MvPolynomial.X j))
  simpa only [Θ, a3r_δD, map_sub, Algebra.TensorProduct.productMap_apply_tmul,
    map_one, mul_one, one_mul, sub_eq_zero] using hj
#print axioms IntersectionProductScaf_generic_small_relative_separates_maps


/-- A codimension-zero point of an integral scheme is its generic point. -/
theorem IntersectionProductScaf_eq_genericPoint_of_coheight_zero
    (Y : Scheme) [IsIntegral Y] (y : Y) (hy : coheight y = 0) :
    y = genericPoint Y := by
  have hle : y ≤ genericPoint Y := Scheme.le_iff_specializes.mpr (genericPoint_specializes y)
  have hrev : genericPoint Y ≤ y := (Order.coheight_eq_zero.mp hy) hle
  exact ((Scheme.le_iff_specializes.mp hrev).antisymm (genericPoint_specializes y)).eq
#print axioms IntersectionProductScaf_eq_genericPoint_of_coheight_zero

/-- A codimension-one point on a constant section is the generic point of that whole section. -/
theorem IntersectionProductScaf_section_coheight_one_whole
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (c : ℂ) (x : X.left) (hx : coheight (a3n_σ X c x) = 1) :
    a3n_σ X c x = a3n_σ X c (genericPoint X.left) := by
  rw [a3n_coheight_σ] at hx
  have hzero : coheight x = 0 := by
    have he : coheight x + 1 = (0 : ℕ∞) + 1 := by simpa only [zero_add] using hx
    exact WithTop.add_right_cancel (show (1 : ℕ∞) ≠ ⊤ from ENat.one_ne_top) he
  rw [IntersectionProductScaf_eq_genericPoint_of_coheight_zero X.left x hzero]
#print axioms IntersectionProductScaf_section_coheight_one_whole

/-- The relative affine chart maps to the complex parameter chart by its tensor coordinates. -/
theorem IntersectionProductScaf_relative_chart_parameter
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (j : Fin (a3s_N X + 1)) :
    a3m_Tκ (a3s_CX X) j ≫ (a3h_e X).inv ≫ a3n_p X =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
        (((a3s_CX X).θ j).comp MvPolynomial.C).toIntAlgHom
        (AlgHom.id ℤ a3m_Away1)).toRingHom) ≫ a3m_Pnκ 1 0 := by
  apply pullback.hom_ext
  · change _ ≫ ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ) = _
    have hp : a3n_p X ≫ ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ) =
        (a3n_q X).left ≫ X.hom := pullback.condition.symm
    rw [Category.assoc, Category.assoc, hp, ← Category.assoc (a3h_e X).inv,
      ← a3h_e_fst, Iso.inv_hom_id_assoc]
    rw [a3m_Tκ, ← Category.assoc, a3m_prodChart_fst, Category.assoc, a3t_chart_over,
      ← Spec.map_comp]
    rw [Category.assoc, a3m_Pnκ, a3m_prodChart_fst, Category.comp_id, ← Spec.map_comp]
    congr 1
  · change _ ≫ a3n_π = _
    rw [Category.assoc, Category.assoc, show a3n_p X ≫ a3n_π = a3n_h X from rfl,
      ← a3h_e_snd, Iso.inv_hom_id_assoc]
    rw [a3m_Tκ, a3m_prodChart_snd, Category.assoc, a3m_Pnκ, a3m_prodChart_snd, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    ext z
    simp [Algebra.TensorProduct.map_tmul]
#print axioms IntersectionProductScaf_relative_chart_parameter

/-- A scalar value of the relative cone parameter places the point on that constant section. -/
theorem IntersectionProductScaf_mem_section_of_parameter_mem
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (y : (a3n_T X).left) (hy : y ∈ a3h_U X) (c : ℂ)
    (hc : MvPolynomial.X (Sum.inr ()) - MvPolynomial.C c ∈ a3h_P X y hy) :
    y ∈ Set.range (a3n_σ X c) := by
  obtain ⟨j, p, hp, he⟩ := a3m_lineCharts_pt (a3s_CX X) (a3s_hov X) (a3h_pt X y hy)
  have he' : y = (a3h_e X).inv (a3m_Tκ (a3s_CX X) j p) := by
    change (a3h_e X).hom y = a3m_Tκ (a3s_CX X) j p at he
    rw [← he, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  let f := Algebra.TensorProduct.map (((a3s_CX X).θ j).comp MvPolynomial.C).toIntAlgHom
    (AlgHom.id ℤ a3m_Away1)
  have hparam : a3n_p X y = a3m_Pnκ 1 0 (Spec.map (CommRingCat.ofHom f.toRingHom) p) := by
    rw [he', ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      IntersectionProductScaf_relative_chart_parameter, Scheme.Hom.comp_apply]
  rw [a3n_range_σ, Set.mem_preimage, hparam]
  apply a3n_mem_range_pt
  change f (a3n_chartEquiv 0 (Polynomial.X - Polynomial.C c)) ∈ p.asIdeal
  have heq : a3m_eq (Fin (a3s_N X + 1))
      (a3h_eqT (Fin (a3s_N X + 1)) (MvPolynomial.X (Sum.inr ()) - MvPolynomial.C c)) =
      MvPolynomial.C (Polynomial.X - Polynomial.C c) := by
    rw [map_sub, a3h_eqT_inr, map_sub, a3m_eq_X, map_sub]
    congr 1
    change (a3m_eq _) ((a3h_eqT _) (algebraMap ℂ _ c)) = algebraMap ℂ _ c
    rw [AlgEquiv.commutes, AlgEquiv.commutes]
  change a3m_eq _ (a3h_eqT _ _) ∈ (a3s_LC X).prime (a3h_pt X y hy) at hc
  rw [heq, (a3s_LC X).mem_prime_iff_of_isHomogeneous _ j p hp _ 0
    (isHomogeneous_C _ _)] at hc
  change a3m_Tθ (a3s_CX X) j (MvPolynomial.C (Polynomial.X - Polynomial.C c)) ∈ p.asIdeal at hc
  convert hc using 1
  simp [f, map_sub, a3n_chartEquiv_X, a3m_Tθ, a3n_chartEquiv,
    Algebra.TensorProduct.map_tmul, a3n_awayEquiv, a3n_ev]
#print axioms IntersectionProductScaf_mem_section_of_parameter_mem


/-- A codimension-one input other than a whole section has no scalar cone parameter. -/
theorem IntersectionProductScaf_codimension_one_parameter_nonconstant
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (y : (a3n_T X).left) (hy : y ∈ a3h_U X) (hc : coheight y = 1)
    (hsec : ∀ c : ℂ, y ≠ a3n_σ X c (genericPoint X.left)) :
    ∀ c : ℂ, MvPolynomial.X (Sum.inr ()) - MvPolynomial.C c ∉ a3h_P X y hy := by
  intro c hmem
  obtain ⟨x, hx⟩ := IntersectionProductScaf_mem_section_of_parameter_mem X y hy c hmem
  apply hsec c
  rw [← hx]
  exact IntersectionProductScaf_section_coheight_one_whole X c x (hx ▸ hc)
#print axioms IntersectionProductScaf_codimension_one_parameter_nonconstant


/-- In codimension at least two, general product projections separate cone maps even on constant parameter fibres. -/
theorem IntersectionProductScaf_generic_point_cone_separates_maps
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {n : ℕ} (hn : Order.height (genericPoint X.left) = n)
    (y : (a3n_T X).left) (hy : y ∈ a3h_U X) (hc : (2 : ℕ∞) ≤ coheight y) :
    a3r_Generic {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ |
      ∀ (K : Type) [Field K] [Algebra ℂ K]
        (φ ψ : (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_P X y hy) →ₐ[ℂ] K),
        Function.Injective φ →
        (∀ i, φ (Ideal.Quotient.mk (a3h_P X y hy)
            (a3r_lin (a3h_block a) (MvPolynomial.X i))) =
          ψ (Ideal.Quotient.mk (a3h_P X y hy)
            (a3r_lin (a3h_block a) (MvPolynomial.X i)))) → φ = ψ} := by
  obtain ⟨c, hcy, hcn, hdim⟩ := a3h_dim_P X n hn y hy
  have htwo : 2 ≤ c := by
    rw [hcy] at hc
    exact_mod_cast hc
  apply IntersectionProductScaf_generic_small_relative_separates_maps
    (a3h_P X y hy) (n + 2 - c) hdim
  simp only [Fintype.card_fin]
  omega
#print axioms IntersectionProductScaf_generic_point_cone_separates_maps

/-- General relative projections have no off-diagonal pair of the input dimension. -/
theorem IntersectionProductScaf_generic_relative_diagonal
    {ρ σ : Type} [Fintype ρ] [Fintype σ]
    (P : Ideal (MvPolynomial (σ ⊕ Unit) ℂ)) [P.IsPrime]
    (hdom : ∀ c : ℂ, MvPolynomial.X (Sum.inr ()) - MvPolynomial.C c ∉ P)
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (σ ⊕ Unit) ℂ ⧸ P) = d)
    (hdim : d ≤ Fintype.card ρ) :
    a3r_Generic {a : ρ × σ → ℂ |
      ∀ Q : Ideal ((MvPolynomial (σ ⊕ Unit) ℂ ⧸ P) ⊗[ℂ]
        (MvPolynomial (σ ⊕ Unit) ℂ ⧸ P)), Q.IsPrime →
      (d : WithBot ℕ∞) ≤ ringKrullDim (_ ⧸ Q) →
      (∀ i, ∑ k, algebraMap ℂ _ (a3h_block a i k) * a3r_δD P P k - 0 ∈ Q) →
      ∀ j, a3r_δD P P j ∈ Q} := by
  let A := MvPolynomial (σ ⊕ Unit) ℂ ⧸ P
  have : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) (Ideal.Quotient.mkₐ_surjective ℂ P)
  refine (a3h_generic_secant_rel (ρ := ρ) P P (fun c => Or.inl (hdom c))).mono ?_
  intro a ha Q hQ hQdim hrel j
  by_contra hj
  have hb := ha j Q hQ hj hrel
  rw [hc9k8_ringKrullDim_tensorProduct, hd, Fintype.card_sum, Fintype.card_unit] at hb
  have hc : (d : WithBot ℕ∞) + (Fintype.card ρ + 1 : ℕ) ≤ (d : WithBot ℕ∞) + d :=
    (add_le_add hQdim le_rfl).trans hb
  have hn : d + (Fintype.card ρ + 1) ≤ d + d := by exact_mod_cast hc
  omega
#print axioms IntersectionProductScaf_generic_relative_diagonal

/-- Relative projections separate injective maps of a sufficiently small cone into a field. -/
theorem IntersectionProductScaf_generic_relative_separates_maps
    {ρ σ : Type} [Fintype ρ] [Fintype σ]
    (P : Ideal (MvPolynomial (σ ⊕ Unit) ℂ)) [P.IsPrime]
    (hdom : ∀ c : ℂ, MvPolynomial.X (Sum.inr ()) - MvPolynomial.C c ∉ P)
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (σ ⊕ Unit) ℂ ⧸ P) = d)
    (hdim : d ≤ Fintype.card ρ) :
    a3r_Generic {a : ρ × σ → ℂ |
      ∀ (K : Type) [Field K] [Algebra ℂ K]
        (φ ψ : (MvPolynomial (σ ⊕ Unit) ℂ ⧸ P) →ₐ[ℂ] K),
        Function.Injective φ →
        (∀ i, φ (Ideal.Quotient.mk P (a3r_lin (a3h_block a) (MvPolynomial.X i))) =
          ψ (Ideal.Quotient.mk P (a3r_lin (a3h_block a) (MvPolynomial.X i)))) → φ = ψ} := by
  classical
  let A := MvPolynomial (σ ⊕ Unit) ℂ ⧸ P
  have : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) (Ideal.Quotient.mkₐ_surjective ℂ P)
  refine (IntersectionProductScaf_generic_relative_diagonal P hdom d hd hdim).mono ?_
  intro a ha K _ _ φ ψ hφ hrel
  let Θ : A ⊗[ℂ] A →ₐ[ℂ] K := Algebra.TensorProduct.productMap φ ψ
  let Q := RingHom.ker Θ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime _
  let ι : A →ₐ[ℂ] (A ⊗[ℂ] A) ⧸ Q :=
    (Ideal.Quotient.mkₐ ℂ Q).comp Algebra.TensorProduct.includeLeft
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply hφ
    rw [map_zero]
    have hh : (x ⊗ₜ[ℂ] (1 : A)) ∈ Q :=
      Ideal.Quotient.eq_zero_iff_mem.mp hx
    simpa only [Q, RingHom.mem_ker, Θ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.productMap_apply_tmul,
      map_one, mul_one] using hh
  have hQdim : (d : WithBot ℕ∞) ≤ ringKrullDim ((A ⊗[ℂ] A) ⧸ Q) := by
    rw [← hd]
    exact a3m_ringKrullDim_le_of_injective ι hι
  have hlinear (i : ρ ⊕ Unit) :
      ∑ k, algebraMap ℂ (A ⊗[ℂ] A) (a3h_block a i k) * a3r_δD P P k - 0 ∈ Q := by
    change Θ _ = 0
    have h := hrel i
    simp only [a3r_lin_X, map_sum, map_mul, ← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap, AlgHom.commutes] at h
    simp only [Θ, map_sub, map_sum, map_mul, AlgHom.commutes, map_zero, sub_zero,
      a3r_δD, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, one_mul,
      mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  have he := ha Q inferInstance hQdim hlinear
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  have hj := he j
  change Θ (a3r_δD P P j) = 0 at hj
  change φ (Ideal.Quotient.mk P (MvPolynomial.X j)) = ψ (Ideal.Quotient.mk P (MvPolynomial.X j))
  simpa only [Θ, a3r_δD, map_sub, Algebra.TensorProduct.productMap_apply_tmul,
    map_one, mul_one, one_mul, sub_eq_zero] using hj
#print axioms IntersectionProductScaf_generic_relative_separates_maps

/-- Every positive-codimension input other than a whole constant section has generically separated cone maps. -/
theorem IntersectionProductScaf_generic_nonsection_cone_separates_maps
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {n : ℕ} (hn : Order.height (genericPoint X.left) = n)
    (y : (a3n_T X).left) (hy : y ∈ a3h_U X) (hc : coheight y ≠ 0)
    (hsec : ∀ c : ℂ, y ≠ a3n_σ X c (genericPoint X.left)) :
    a3r_Generic {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ |
      ∀ (K : Type) [Field K] [Algebra ℂ K]
        (φ ψ : (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_P X y hy) →ₐ[ℂ] K),
        Function.Injective φ →
        (∀ i, φ (Ideal.Quotient.mk (a3h_P X y hy)
            (a3r_lin (a3h_block a) (MvPolynomial.X i))) =
          ψ (Ideal.Quotient.mk (a3h_P X y hy)
            (a3r_lin (a3h_block a) (MvPolynomial.X i)))) → φ = ψ} := by
  by_cases htwo : (2 : ℕ∞) ≤ coheight y
  · exact IntersectionProductScaf_generic_point_cone_separates_maps X hn y hy htwo
  obtain ⟨c, hcy, hcn, hdim⟩ := a3h_dim_P X n hn y hy
  have hc0 : c ≠ 0 := by
    intro h
    apply hc
    simp only [hcy, h, Nat.cast_zero]
  have hc2 : ¬ 2 ≤ c := by
    intro h
    apply htwo
    rw [hcy]
    exact_mod_cast h
  have hc1 : c = 1 := by omega
  have hy1 : coheight y = 1 := by simpa only [hc1, Nat.cast_one] using hcy
  apply IntersectionProductScaf_generic_relative_separates_maps (a3h_P X y hy)
    (IntersectionProductScaf_codimension_one_parameter_nonconstant X y hy hy1 hsec)
    (n + 2 - c) hdim
  simp only [Fintype.card_fin, hc1]
  omega
#print axioms IntersectionProductScaf_generic_nonsection_cone_separates_maps

/-- Separation on a domain determines the degree of its fraction field over a field containing the selected elements. -/
theorem IntersectionProductScaf_finrank_one_of_fraction_maps
    {ι : Type} (A K L : Type) [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra ℂ A] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] [Algebra A L] [IsScalarTower ℂ A L] [IsFractionRing A L]
    [Module.Finite K L] [CharZero K]
    (u : ι → A) (hu : ∀ i, ∃ k : K, algebraMap K L k = algebraMap A L (u i))
    (hsep : ∀ (E : Type) [Field E] [Algebra ℂ E] (φ ψ : A →ₐ[ℂ] E),
      Function.Injective φ → (∀ i, φ (u i) = ψ (u i)) → φ = ψ) :
    Module.finrank K L = 1 := by
  let E := AlgebraicClosure L
  haveI : Subsingleton (L →ₐ[K] E) := ⟨by
    intro φ ψ
    have he := hsep E ((φ.restrictScalars ℂ).comp (IsScalarTower.toAlgHom ℂ A L))
      ((ψ.restrictScalars ℂ).comp (IsScalarTower.toAlgHom ℂ A L))
      (φ.injective.comp (IsFractionRing.injective A L)) (by
        intro i
        obtain ⟨k, hk⟩ := hu i
        change φ (algebraMap A L (u i)) = ψ (algebraMap A L (u i))
        rw [← hk, φ.commutes, ψ.commutes])
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext x
    exact congrArg (fun f : A →ₐ[ℂ] E => f x) he⟩
  haveI : Nonempty (L →ₐ[K] E) := ⟨IsScalarTower.toAlgHom K L E⟩
  rw [← AlgHom.card K L E]
  exact Fintype.card_eq_one_iff.mpr ⟨IsScalarTower.toAlgHom K L E, fun _ => Subsingleton.elim _ _⟩
#print axioms IntersectionProductScaf_finrank_one_of_fraction_maps


end PointConeSeparation
end HodgeLean.Adapters
