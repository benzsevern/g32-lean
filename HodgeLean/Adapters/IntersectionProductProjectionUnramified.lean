import HodgeLean.Adapters.IntersectionProductConeSeparation
import HodgeLean.Adapters.IntersectionProductBlochProjection
import HodgeLean.Adapters.IntersectionProductBlochAssembly
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
/-! # Generic unramified neighborhoods of projection cone points

The spatial cone statement specializes Roberts' differential-rank argument;
the relative statement keeps the parameter fixed under base change.
Source: J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970*
(1972), 89–96, Main Lemma.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Order MvPolynomial TensorProduct
namespace HodgeLean.Adapters
local instance projectionUnramifiedDecidableEq (A : Type*) : DecidableEq A := Classical.decEq A
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000 in
/-- A general finite projection is unramified on a neighborhood of the spatial cone point. -/
theorem IntersectionProductScaf_generic_spatial_cone_unramified_neighborhood
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {n : ℕ} (hn : Order.height (genericPoint X.left) = n) (x : X.left) :
    a3r_Generic {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ |
      ∀ hfin : ((Ideal.Quotient.mk (a3s_IX X)).comp
        (a3r_lin (a3r_mat a)).toRingHom).Finite,
      ∃ f : MvPolynomial (Fin (a3s_N X + 1)) ℂ,
        f ∉ (a3s_CX X).prime x ∧
        letI : Algebra (MvPolynomial (Fin (n + 1)) ℂ)
            (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) :=
          ((Ideal.Quotient.mk (a3s_IX X)).comp
            (a3r_lin (a3r_mat a)).toRingHom).toAlgebra
        Algebra.FormallyUnramified (MvPolynomial (Fin (n + 1)) ℂ)
          (Localization.Away (Ideal.Quotient.mk (a3s_IX X) f))} := by
  let P := (a3s_CX X).prime x
  have hP : P.IsPrime := (a3s_CX X).isPrime_prime x
  have hIP : a3s_IX X ≤ P := a3s_IX_le X x
  let Q := P.map (Ideal.Quotient.mk (a3s_IX X))
  have hQ : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker])
  have hcomap : Q.comap (Ideal.Quotient.mk (a3s_IX X)) = P := by
    dsimp only [Q]
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hIP]
  obtain ⟨j, hj⟩ := a3s_relevant X x
  have hjQ : Ideal.Quotient.mk (a3s_IX X) (MvPolynomial.X j) ∉ Q := by
    rw [← Ideal.mem_comap, hcomap]
    exact hj
  refine (a3r_generic_isUnramifiedAt (ρ := Fin (n + 1)) (a3s_IX X) Q
    ((a3m_roberts_rank X n hn Q ⟨j, hjQ⟩).trans (by simp))).mono ?_
  intro a ha hfin
  let _ : Algebra (MvPolynomial (Fin (n + 1)) ℂ)
      (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) :=
    ((Ideal.Quotient.mk (a3s_IX X)).comp (a3r_lin (a3r_mat a)).toRingHom).toAlgebra
  have : Algebra.IsUnramifiedAt (MvPolynomial (Fin (n + 1)) ℂ) Q := ha
  have : Algebra.FiniteType (MvPolynomial (Fin (n + 1)) ℂ)
      (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) := hfin.to_finiteType
  have : Algebra.EssFiniteType (MvPolynomial (Fin (n + 1)) ℂ)
      (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) :=
    Algebra.EssFiniteType.of_finiteType _ _
  obtain ⟨f, hf, hfun⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt
    (R := MvPolynomial (Fin (n + 1)) ℂ) Q
  obtain ⟨f₀, rfl⟩ := Ideal.Quotient.mk_surjective f
  refine ⟨f₀, ?_, hfun⟩
  intro hm
  apply hf
  rw [← Ideal.mem_comap, hcomap]
  exact hm
#print axioms IntersectionProductScaf_generic_spatial_cone_unramified_neighborhood
/-- A general projection has an unramified neighborhood of the relevant relative cone point. -/
theorem IntersectionProductScaf_generic_point_cone_unramified_neighborhood
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {n : ℕ} (hn : Order.height (genericPoint X.left) = n)
    (y : (a3n_T X).left) (hy : y ∈ a3h_U X) :
    a3r_Generic {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ |
      ∀ hfin : ((Ideal.Quotient.mk (a3s_IX X)).comp
        (a3r_lin (a3r_mat a)).toRingHom).Finite,
      ∃ f : MvPolynomial (Fin (a3s_N X + 1)) ℂ,
        rename Sum.inl f ∉ a3h_P X y hy ∧
        letI : Algebra (MvPolynomial (Fin (n + 1) ⊕ Unit) ℂ)
            (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_IXr (a3s_IX X)) :=
          ((Ideal.Quotient.mk (a3h_IXr (a3s_IX X))).comp
            (a3r_lin (a3h_block a)).toRingHom).toAlgebra
        Algebra.FormallyUnramified (MvPolynomial (Fin (n + 1) ⊕ Unit) ℂ)
          (Localization.Away (Ideal.Quotient.mk (a3h_IXr (a3s_IX X)) (rename Sum.inl f)))} := by
  refine (IntersectionProductScaf_generic_spatial_cone_unramified_neighborhood
    X hn ((a3n_q X).left y)).mono ?_
  intro a ha hfin
  obtain ⟨f, hf, hun⟩ := ha hfin
  refine ⟨f, ?_, a3h_formallyUnramified_rel (a3s_IX X) a f hun⟩
  rw [← a3h_fst_prime X y hy]
  exact hf
#print axioms IntersectionProductScaf_generic_point_cone_unramified_neighborhood

/-- Adding coordinate values to a spanning differential family gives generic spanning in one extra dimension. -/
theorem IntersectionProductScaf_generic_augmented_span
    {ρ σ K V : Type} [Fintype ρ] [Fintype σ] [DecidableEq σ]
    [Field K] [Algebra ℂ K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (v : σ → V) (x : σ → K) (j : σ)
    (hv : Submodule.span K (Set.range v) = ⊤) (hvj : v j = 0) (hxj : x j = 1)
    (hdim : Module.finrank K V + 1 ≤ Fintype.card ρ) :
    a3r_Generic {a : ρ × σ → ℂ |
      Submodule.span K (Set.range fun i => ∑ k, algebraMap ℂ K (a (i, k)) • (v k, x k)) = ⊤} := by
  let S : Submodule K (V × K) := Submodule.span K (Set.range fun k => (v k, x k))
  have hj : (0, 1) ∈ S := by
    have h : (v j, x j) ∈ S := Submodule.subset_span (Set.mem_range_self j)
    rwa [hvj, hxj] at h
  have hgen (k : σ) : (v k, 0) ∈ S := by
    have h := S.sub_mem (Submodule.subset_span (Set.mem_range_self k)) (S.smul_mem (x k) hj)
    simpa using h
  have hV (z : V) : (z, 0) ∈ S := by
    have hz : z ∈ Submodule.span K (Set.range v) := hv ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨k, rfl⟩ := hz; exact hgen k
    | zero => exact S.zero_mem
    | add z z' _ _ hz hz' => simpa using S.add_mem hz hz'
    | smul c z _ hz => simpa using S.smul_mem c hz
  have hspan : S = ⊤ := by
    apply top_unique
    rintro ⟨z, c⟩ _
    have h := S.add_mem (hV z) (S.smul_mem c hj)
    simpa using h
  apply a3r_generic_span (fun k => (v k, x k)) hspan
  simpa only [Module.finrank_prod, Module.finrank_self] using hdim
#print axioms IntersectionProductScaf_generic_augmented_span

/-- General linear coordinates span values and differentials at every fixed smooth affine chart point. -/
theorem IntersectionProductScaf_generic_chart_differentials
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {n : ℕ} (hn : Order.height (genericPoint X.left) = n)
    (j : Fin (a3s_N X + 1)) (p : Spec ((a3s_CX X).T j)) :
    letI : p.asIdeal.IsPrime := p.isPrime
    letI : Algebra ℂ ((a3s_CX X).T j) := (((a3s_CX X).θ j).comp MvPolynomial.C).toAlgebra
    a3r_Generic {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ |
      Submodule.span p.asIdeal.ResidueField (Set.range fun i =>
        ∑ k, algebraMap ℂ p.asIdeal.ResidueField (a (i, k)) •
          ((1 : p.asIdeal.ResidueField) ⊗ₜ[(a3s_CX X).T j]
            KaehlerDifferential.D ℂ ((a3s_CX X).T j) ((a3s_CX X).θ j (MvPolynomial.X k)),
            algebraMap ((a3s_CX X).T j) p.asIdeal.ResidueField
              ((a3s_CX X).θ j (MvPolynomial.X k)))) = ⊤} := by
  let : p.asIdeal.IsPrime := p.isPrime
  let : Algebra ℂ ((a3s_CX X).T j) := (((a3s_CX X).θ j).comp MvPolynomial.C).toAlgebra
  let T := (a3s_CX X).T j
  let K := p.asIdeal.ResidueField
  let θ : MvPolynomial (Fin (a3s_N X + 1)) ℂ →ₐ[ℂ] T :=
    { (a3s_CX X).θ j with commutes' := fun _ => rfl }
  have : Algebra.FiniteType ℂ T := Algebra.FiniteType.of_surjective θ ((a3s_CX X).θ_surj j)
  have : Nonempty (Spec T) := ⟨p⟩
  have : IsIntegral (Spec T) := isIntegral_of_isOpenImmersion ((a3s_CX X).κ j)
  have : IsDomain T := (affine_isIntegral_iff T).1 inferInstance
  have : Algebra.Smooth ℂ T := a3t_chart_smooth X j
  have hdim : ringKrullDim T = n := by
    have h1 := a3m_height_openImmersion (Y := X) ((a3s_CX X).κ j) (genericPoint (Spec T))
    rw [genericPoint_eq_of_isOpenImmersion, hn] at h1
    have h2 := hc9k8_height_spec T (genericPoint (Spec T))
    rw [← h1, genericPoint_eq_bot_of_affine] at h2
    rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot T)]
    exact h2.symm
  have hD : Submodule.span T (Set.range fun k =>
      KaehlerDifferential.D ℂ T (θ (MvPolynomial.X k))) = ⊤ := by
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation ℂ T, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    obtain ⟨F, rfl⟩ := (a3s_CX X).θ_surj j r
    change KaehlerDifferential.D ℂ T (θ F) ∈ _
    induction F using MvPolynomial.induction_on with
    | C c =>
      change KaehlerDifferential.D ℂ T (algebraMap ℂ T c) ∈ _
      rw [Derivation.map_algebraMap]
      exact zero_mem _
    | add F G hF hG => rw [map_add, map_add]; exact add_mem hF hG
    | mul_X F k hF =>
      rw [map_mul, Derivation.leibniz]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
        (Submodule.smul_mem _ _ hF)
  have hV : Submodule.span K (Set.range fun k =>
      (1 : K) ⊗ₜ[T] KaehlerDifferential.D ℂ T (θ (MvPolynomial.X k))) = ⊤ := by
    simpa only [← Set.range_comp, Function.comp_def] using a3t_span_one_tmul (K := K) _ hD
  apply IntersectionProductScaf_generic_augmented_span _ _ j hV
  · change (1 : K) ⊗ₜ[T] KaehlerDifferential.D ℂ T ((a3s_CX X).θ j (MvPolynomial.X j)) = 0
    rw [(a3s_CX X).θ_X_self, Derivation.map_one_eq_zero, tmul_zero]
  · change algebraMap T K ((a3s_CX X).θ j (MvPolynomial.X j)) = 1
    rw [(a3s_CX X).θ_X_self, map_one]
  · simpa only [Fintype.card_fin] using Nat.add_le_add_right (a3t_finrank_le_of_smooth (K := K) n hdim) 1
#print axioms IntersectionProductScaf_generic_chart_differentials

/-- Spanning coordinate values and differentials forces an unramified local map when their ratios come from the base. -/
theorem IntersectionProductScaf_formallyUnramified_of_normalized_differentials
    {ι : Type} (T R B : Type) [CommRing T] [CommRing R] [CommRing B] [IsLocalRing B]
    [Algebra ℂ T] [Algebra ℂ R] [Algebra ℂ B] [Algebra T B] [Algebra R B]
    [IsScalarTower ℂ T B] [IsScalarTower ℂ R B] [Algebra.FormallyEtale T B]
    [Module.Finite B Ω[B⁄R]]
    (u : ι → T) (s : T) (w : ι → R)
    (hs : algebraMap T (IsLocalRing.ResidueField B) s ≠ 0)
    (hu : ∀ i, algebraMap T B (u i) = algebraMap T B s * algebraMap R B (w i))
    (hspan : Submodule.span (IsLocalRing.ResidueField B) (Set.range fun i =>
      ((1 : IsLocalRing.ResidueField B) ⊗ₜ[T] KaehlerDifferential.D ℂ T (u i),
        algebraMap T (IsLocalRing.ResidueField B) (u i))) = ⊤) :
    Algebra.FormallyUnramified R B := by
  let K := IsLocalRing.ResidueField B
  let V := K ⊗[T] Ω[T⁄ℂ]
  let W := K ⊗[B] Ω[B⁄R]
  let e₁ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ T B
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange T B K K Ω[T⁄ℂ]
  let e₃ := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e₁
  let e := e₂.symm.trans e₃
  let L : V →ₗ[K] W := ((KaehlerDifferential.map ℂ R B B).baseChange K).comp e.toLinearMap
  have hLsurj : Function.Surjective L := by
    have hb : Function.Surjective ((KaehlerDifferential.map ℂ R B B).baseChange K) := by
      rw [LinearMap.baseChange_eq_lTensor]
      exact LinearMap.lTensor_surjective K (KaehlerDifferential.map_surjective ℂ R B)
    exact hb.comp e.surjective
  have hL (r : T) : L ((1 : K) ⊗ₜ[T] KaehlerDifferential.D ℂ T r) =
      (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (algebraMap T B r) := by
    change ((KaehlerDifferential.map ℂ R B B).baseChange K)
      (e₃ (e₂.symm ((1 : K) ⊗ₜ[T] KaehlerDifferential.D ℂ T r))) = _
    simp only [e₁, e₂, e₃,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D,
      LinearMap.baseChange_tmul]
    rfl
  let d : W := (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (algebraMap T B s)
  let z : W := (algebraMap T K s)⁻¹ • d
  have hrel (i : ι) : L ((1 : K) ⊗ₜ[T] KaehlerDifferential.D ℂ T (u i)) =
      algebraMap T K (u i) • z := by
    rw [hL, hu, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, zero_add]
    have he : algebraMap T K (u i) = algebraMap T K s * algebraMap B K (algebraMap R B (w i)) := by
      rw [IsScalarTower.algebraMap_apply T B K, hu, map_mul,
        ← IsScalarTower.algebraMap_apply T B K]
    change (1 : K) ⊗ₜ[B] (algebraMap R B (w i) • _) = _
    rw [← TensorProduct.smul_tmul, ← algebraMap_smul K, smul_eq_mul, mul_one]
    rw [show algebraMap B K (algebraMap R B (w i)) ⊗ₜ[B]
        KaehlerDifferential.D R B (algebraMap T B s) =
        algebraMap B K (algebraMap R B (w i)) • d by
      dsimp only [d]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    dsimp only [z]
    rw [smul_smul, he]
    congr 1
    rw [mul_comm (algebraMap T K s), mul_assoc, mul_inv_cancel₀ hs, mul_one]
  let F : V × K →ₗ[K] W := L.comp (LinearMap.fst K V K) -
    (LinearMap.toSpanSingleton K W z).comp (LinearMap.snd K V K)
  have hF : F = 0 := by
    apply LinearMap.ext_on_range hspan
    intro i
    change L ((1 : K) ⊗ₜ[T] KaehlerDifferential.D ℂ T (u i)) -
      algebraMap T K (u i) • z = 0
    rw [hrel, sub_self]
  have hLzero (v : V) : L v = 0 := by
    have hh := congrArg (fun m : V × K →ₗ[K] W => m (v, 0)) hF
    simpa only [F, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, LinearMap.toSpanSingleton_apply, zero_smul, sub_zero,
      LinearMap.zero_apply] using hh
  have hW : Subsingleton W := ⟨fun x y => by
    obtain ⟨x, rfl⟩ := hLsurj x
    obtain ⟨y, rfl⟩ := hLsurj y
    rw [hLzero, hLzero]⟩
  exact ⟨IsLocalRing.subsingleton_tensorProduct.mp hW⟩
#print axioms IntersectionProductScaf_formallyUnramified_of_normalized_differentials

set_option maxHeartbeats 400000 in
/-- General projective coordinate ratios give an unramified map into the local ring of a fixed smooth chart point. -/
theorem IntersectionProductScaf_generic_projection_chart_stalk_unramified
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {n : ℕ} (hn : Order.height (genericPoint X.left) = n)
    (j : Fin (a3s_N X + 1)) (p : Spec ((a3s_CX X).T j)) :
    a3r_Generic {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ |
      ∀ (i : Fin (n + 1)) (hs : a3h_s X (a3r_mat a) j i ∉ p.asIdeal),
        letI : p.asIdeal.IsPrime := p.isPrime
        let f : Localization.Away (a3h_s X (a3r_mat a) j i) →+* Localization.AtPrime p.asIdeal :=
          IsLocalization.Away.lift (a3h_s X (a3r_mat a) j i)
            (IsLocalization.map_units (Localization.AtPrime p.asIdeal)
              (⟨a3h_s X (a3r_mat a) j i, hs⟩ : p.asIdeal.primeCompl))
        (f.comp (a3h_ψ X (a3r_mat a) j i)).FormallyUnramified} := by
  let : p.asIdeal.IsPrime := p.isPrime
  let : Algebra ℂ ((a3s_CX X).T j) := (((a3s_CX X).θ j).comp MvPolynomial.C).toAlgebra
  refine (IntersectionProductScaf_generic_chart_differentials X hn j p).mono ?_
  intro a ha i hs
  let T := (a3s_CX X).T j
  let B := Localization.AtPrime p.asIdeal
  let R := a3m_PnT n i
  let s := a3h_s X (a3r_mat a) j i
  let f : Localization.Away s →+* B := IsLocalization.Away.lift s
    (IsLocalization.map_units B (⟨s, hs⟩ : p.asIdeal.primeCompl))
  let g : R →+* B := f.comp (a3h_ψ X (a3r_mat a) j i)
  let : Algebra ℂ R := ((a3m_Pnθ n i).comp MvPolynomial.C).toAlgebra
  let : Algebra R B := g.toAlgebra
  let : SMul ℂ R := (inferInstance : Algebra ℂ R).toSMul
  let : SMul ℂ B := (inferInstance : Algebra ℂ B).toSMul
  have hf (r : T) : f (algebraMap T (Localization.Away s) r) = algebraMap T B r :=
    IsLocalization.Away.lift_eq s _ r
  have : IsScalarTower ℂ R B := by
    refine IsScalarTower.of_algebraMap_eq (R := ℂ) (S := R) (A := B) fun c => ?_
    have h := a3h_ψ_θ X (ℓ := a3r_mat a) j i (MvPolynomial.C c) 0 (isHomogeneous_C _ _)
    simp only [a3r_lin_C, pow_zero, one_mul] at h
    have hh := congrArg f h
    rw [hf] at hh
    exact hh
  have : Algebra.FiniteType ℂ T := Algebra.FiniteType.of_surjective
    ({ (a3s_CX X).θ j with commutes' := fun _ => rfl } : MvPolynomial (Fin (a3s_N X + 1)) ℂ →ₐ[ℂ] T)
    ((a3s_CX X).θ_surj j)
  have : Algebra.FormallyEtale T B := Algebra.FormallyEtale.of_isLocalization p.asIdeal.primeCompl
  have : Module.Finite B Ω[B⁄ℂ] := inferInstance
  have : Module.Finite B Ω[B⁄R] := Module.Finite.of_surjective
    (KaehlerDifferential.map ℂ R B B) (KaehlerDifferential.map_surjective ℂ R B)
  let u (k : Fin (n + 1)) : T := (a3s_CX X).θ j (a3r_lin (a3r_mat a) (MvPolynomial.X k))
  let w (k : Fin (n + 1)) : R := a3m_Pnθ n i (MvPolynomial.X k)
  have hu (k : Fin (n + 1)) : algebraMap T B (u k) = algebraMap T B s * algebraMap R B (w k) := by
    have h := a3h_ψ_θ X (ℓ := a3r_mat a) j i (MvPolynomial.X k) 1 (isHomogeneous_X _ _)
    simp only [pow_one] at h
    have hh := congrArg f h
    change f (algebraMap T (Localization.Away s) (u k)) =
      f (algebraMap T (Localization.Away s) s * (a3h_ψ X (a3r_mat a) j i) (w k)) at hh
    rw [map_mul, hf, hf] at hh
    exact hh
  have hsK : algebraMap T (IsLocalRing.ResidueField B) s ≠ 0 := by
    exact Ideal.algebraMap_residueField_eq_zero.not.mpr hs
  have hlin (k : Fin (n + 1)) : u k =
      ∑ l, a (k, l) • ((a3s_CX X).θ j (MvPolynomial.X l)) := by
    simp only [u, a3r_lin_X, map_sum, map_mul, Algebra.smul_def]
    rfl
  have hspan : Submodule.span (IsLocalRing.ResidueField B) (Set.range fun k =>
      ((1 : IsLocalRing.ResidueField B) ⊗ₜ[T] KaehlerDifferential.D ℂ T (u k),
        algebraMap T (IsLocalRing.ResidueField B) (u k))) = ⊤ := by
    have hpair (k : Fin (n + 1)) :
        ((1 : IsLocalRing.ResidueField B) ⊗ₜ[T] KaehlerDifferential.D ℂ T (u k),
          algebraMap T (IsLocalRing.ResidueField B) (u k)) =
        ∑ l, algebraMap ℂ (IsLocalRing.ResidueField B) (a (k, l)) •
          ((1 : IsLocalRing.ResidueField B) ⊗ₜ[T]
            KaehlerDifferential.D ℂ T ((a3s_CX X).θ j (MvPolynomial.X l)),
            algebraMap T (IsLocalRing.ResidueField B) ((a3s_CX X).θ j (MvPolynomial.X l))) := by
      apply Prod.ext
      · simp only [Prod.fst_sum, Prod.smul_fst, hlin, map_sum, Derivation.map_smul, tmul_sum]
        apply Finset.sum_congr rfl
        intro l _
        erw [← TensorProduct.smul_tmul, ← algebraMap_smul (IsLocalRing.ResidueField B),
          smul_eq_mul, mul_one]
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      · simp only [Prod.snd_sum, Prod.smul_snd, hlin, map_sum, Algebra.smul_def, map_mul]
        apply Finset.sum_congr rfl
        intro l _
        congr 1

    simp_rw [hpair]
    exact ha
  change Algebra.FormallyUnramified R B
  exact IntersectionProductScaf_formallyUnramified_of_normalized_differentials T R B u s w hsK hu hspan
#print axioms IntersectionProductScaf_generic_projection_chart_stalk_unramified

/-- Unramifiedness of the original local ring transfers to the corresponding point of a localization. -/
theorem IntersectionProductScaf_unramified_at_localization_of_stalk
    (T R A : Type) [CommRing T] [CommRing R] [CommRing A] [Algebra T A]
    (M : Submonoid T) [IsLocalization M A] (p : Ideal A) [p.IsPrime]
    (pT : Ideal T) [pT.IsPrime] (hp : p.comap (algebraMap T A) = pT)
    (g : R →+* A)
    (f : A →+* Localization.AtPrime pT)
    (hf : ∀ t, f (algebraMap T A t) =
      algebraMap T (Localization.AtPrime pT) t)
    (hun : (f.comp g).FormallyUnramified) :
    letI : Algebra R A := g.toAlgebra
    Algebra.IsUnramifiedAt R p := by
  subst pT
  let : Algebra R A := g.toAlgebra
  let B := Localization.AtPrime (p.comap (algebraMap T A))
  let L := Localization.AtPrime p
  have : IsLocalization (p.comap (algebraMap T A)).primeCompl L :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M L p
  let e : B ≃ₐ[T] L := IsLocalization.algEquiv (p.comap (algebraMap T A)).primeCompl B L
  have he : e.toRingHom.comp f = algebraMap A L := by
    apply IsLocalization.ringHom_ext M
    ext t
    change e (f (algebraMap T A t)) = algebraMap A L (algebraMap T A t)
    rw [hf, e.commutes, ← IsScalarTower.algebraMap_apply T A L]
  change Algebra.FormallyUnramified R L
  rw [← RingHom.formallyUnramified_algebraMap]
  change ((algebraMap A L).comp g).FormallyUnramified
  rw [← he, RingHom.comp_assoc]
  exact hun.comp (RingHom.FormallyUnramified.of_surjective e.surjective)
#print axioms IntersectionProductScaf_unramified_at_localization_of_stalk

/-- Unramifiedness of a stalk map can be checked after an open immersion at its source point. -/
theorem IntersectionProductScaf_stalk_unramified_of_open_source
    {U X Y : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] (f : X ⟶ Y) (u : U)
    (hun : ((j ≫ f).stalkMap u).hom.FormallyUnramified) :
    (f.stalkMap (j u)).hom.FormallyUnramified := by
  have he : (j ≫ f).stalkMap u ≫ inv (j.stalkMap u) = f.stalkMap (j u) := by
    rw [Scheme.Hom.stalkMap_comp]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← he]
  exact hun.comp (RingHom.FormallyUnramified.of_surjective
    (ConcreteCategory.bijective_of_isIso (inv (j.stalkMap u))).2)
#print axioms IntersectionProductScaf_stalk_unramified_of_open_source

set_option maxHeartbeats 400000 in
/-- A general finite projection is unramified on an affine neighborhood of a prescribed spatial point. -/
theorem IntersectionProductScaf_generic_projection_unramified_neighborhood
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {n : ℕ} (hn : Order.height (genericPoint X.left) = n) (x : X.left) :
    a3r_Generic {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ |
      ∀ hfin : ((Ideal.Quotient.mk (a3s_IX X)).comp (a3r_lin (a3r_mat a)).toRingHom).Finite,
        ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ X.left),
          IsOpenImmersion j ∧ x ∈ Set.range j ∧
            FormallyUnramified (j ≫ (a3h_πO X hfin).left)} := by
  obtain ⟨j, p, hp⟩ := (a3s_CX X).cover x
  refine (IntersectionProductScaf_generic_projection_chart_stalk_unramified X hn j p).mono ?_
  intro a ha hfin
  obtain ⟨i, hi⟩ := a3h_exists_notMem X (a3r_mat a) hfin x
  have hs : a3h_s X (a3r_mat a) j i ∉ p.asIdeal := by
    rwa [← (a3s_CX X).mem_prime_iff_of_isHomogeneous x j p hp _ 1
      (a3r_lin_X_isHomogeneous (a3r_mat a) i)]
  let T := (a3s_CX X).T j
  let A := a3h_Rs X (a3r_mat a) j i
  let R := a3m_PnT n i
  let s := a3h_s X (a3r_mat a) j i
  obtain ⟨q, hq⟩ : ∃ q : Spec A,
      PrimeSpectrum.comap (algebraMap T (Localization.Away s)) q = p :=
    (PrimeSpectrum.localization_away_comap_range (Localization.Away s) s).ge
      ((PrimeSpectrum.mem_basicOpen _ _).2 hs)
  let : p.asIdeal.IsPrime := p.isPrime
  let : q.asIdeal.IsPrime := q.isPrime
  let g := a3h_ψ X (a3r_mat a) j i
  let f : A →+* Localization.AtPrime p.asIdeal := IsLocalization.Away.lift s
    (IsLocalization.map_units (Localization.AtPrime p.asIdeal) (⟨s, hs⟩ : p.asIdeal.primeCompl))
  let : Algebra R A := g.toAlgebra
  have hI : q.asIdeal.comap (algebraMap T A) = p.asIdeal := congrArg PrimeSpectrum.asIdeal hq
  have hun : Algebra.IsUnramifiedAt R q.asIdeal :=
    IntersectionProductScaf_unramified_at_localization_of_stalk T R A (Submonoid.powers s)
      q.asIdeal p.asIdeal hI g f (fun r => IsLocalization.Away.lift_eq s _ r) (ha i hs)
  let r := a3h_ιs X (a3r_mat a) j i ≫ (a3s_CX X).κ j
  have : IsOpenImmersion (a3h_ιs X (a3r_mat a) j i) := by
    unfold a3h_ιs
    infer_instance
  have : IsOpenImmersion r := inferInstanceAs
    (IsOpenImmersion (a3h_ιs X (a3r_mat a) j i ≫ (a3s_CX X).κ j))
  have he : r ≫ (a3h_πO X hfin).left = Spec.map (CommRingCat.ofHom g) ≫ a3m_Pnκ n i :=
    (a3h_chart X hfin j i).symm
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom g) ≫ a3m_Pnκ n i) := by
    rw [← he]
    infer_instance
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom g)) :=
    locallyOfFiniteType_of_comp _ (a3m_Pnκ n i)
  have hft : g.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := CommRingCat.ofHom g)).mp inferInstance
  have : Algebra.FiniteType R A := hft
  have : Algebra.EssFiniteType R A := Algebra.EssFiniteType.of_finiteType _ _
  obtain ⟨b, hb, hunb⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := R) q.asIdeal
  let B := Localization.Away b
  let k := Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ r
  have hk : k ≫ (a3h_πO X hfin).left =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ a3m_Pnκ n i := by
    change (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ r) ≫ _ = _
    rw [Category.assoc, he, ← Category.assoc, ← Spec.map_comp]
    rfl
  have : FormallyUnramified (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mpr
      (RingHom.formallyUnramified_algebraMap.mpr hunb)
  obtain ⟨q', hq'⟩ : ∃ q' : Spec (.of B),
      PrimeSpectrum.comap (algebraMap A B) q' = q :=
    (PrimeSpectrum.localization_away_comap_range B b).ge ((PrimeSpectrum.mem_basicOpen _ _).2 hb)
  refine ⟨.of B, k, inferInstance, ⟨q', ?_⟩, ?_⟩
  · change (a3s_CX X).κ j (PrimeSpectrum.comap (algebraMap T A)
      (PrimeSpectrum.comap (algebraMap A B) q')) = x
    rw [hq', hq, hp]
  · rw [hk]
    exact MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance inferInstance
#print axioms IntersectionProductScaf_generic_projection_unramified_neighborhood

end HodgeLean.Adapters
