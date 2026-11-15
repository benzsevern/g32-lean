import Mathlib.RepresentationTheory.Character
import HodgeLean.Foundations.Program.PrymParabolicRealizationDefs
import HodgeLean.Foundations.Program.PrymVariationLattice
import HodgeLean.Foundations.Program.PrymVariationCentreRootWeights

noncomputable section

open Module HodgeLean.Papers
open scoped Classical

namespace HodgeLean.Foundations.Program

theorem hg2_trace_surjective {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]
    (f : V →ₗ[R] W) [Module.Free R (LinearMap.ker f)] [Module.Finite R (LinearMap.ker f)]
    (hf : Function.Surjective f) (T : Module.End R V) (U : Module.End R W)
    (hcomm : f ∘ₗ T = U ∘ₗ f) :
    LinearMap.trace R V T =
      LinearMap.trace R (LinearMap.ker f)
        (T.restrict (p := LinearMap.ker f) (q := LinearMap.ker f) (by
          intro z hz
          change f (T z) = 0
          have h := LinearMap.congr_fun hcomm z
          simpa only [LinearMap.comp_apply, LinearMap.mem_ker.mp hz, map_zero] using h)) +
        LinearMap.trace R W U := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f (LinearMap.id : W →ₗ[R] W) hf
  let p : V →ₗ[R] LinearMap.ker f := (LinearMap.id - s ∘ₗ f).codRestrict _ (by
    intro z
    change f (z - s (f z)) = 0
    rw [map_sub]
    have h := LinearMap.congr_fun hs (f z)
    simpa only [LinearMap.comp_apply, LinearMap.id_apply, sub_eq_zero] using h.symm)
  have hsplit : T = (T ∘ₗ (LinearMap.ker f).subtype) ∘ₗ p + (T ∘ₗ s) ∘ₗ f := by
    ext z
    simp [p]
  conv_lhs => rw [hsplit, map_add]
  congr 1
  · rw [LinearMap.trace_comp_comm']
    congr 1
    ext z
    change T z.1 - s (f (T z.1)) = T z.1
    have h := LinearMap.congr_fun hcomm z.1
    have hz : f z.1 = 0 := z.2
    simp only [LinearMap.comp_apply, hz, map_zero] at h
    rw [h, map_zero, sub_zero]
  · rw [LinearMap.trace_comp_comm']
    congr 1
    rw [← LinearMap.comp_assoc, hcomm, LinearMap.comp_assoc, hs, LinearMap.comp_id]

theorem hg2_trace_lmapDomain {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I] (f : I → I) :
    LinearMap.trace R (I →₀ R) (Finsupp.lmapDomain R R f) =
      ∑ i : I, if f i = i then (1 : R) else 0 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace R (Finsupp.basisSingleOne : Basis I R (I →₀ R))]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Finsupp.single_apply]

theorem hg2_trace_exact {R A B C : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [Module.Free R A] [Module.Finite R A]
    [AddCommGroup B] [Module R B] [Module.Free R B] [Module.Finite R B]
    [AddCommGroup C] [Module R C] [Module.Free R C] [Module.Finite R C]
    (i : A →ₗ[R] B) (q : B →ₗ[R] C) [Module.Free R (LinearMap.ker q)]
    [Module.Finite R (LinearMap.ker q)] (hi : Function.Injective i)
    (hq : Function.Surjective q) (hex : LinearMap.range i = LinearMap.ker q)
    (TA : Module.End R A) (TB : Module.End R B) (TC : Module.End R C)
    (hleft : TB ∘ₗ i = i ∘ₗ TA) (hright : q ∘ₗ TB = TC ∘ₗ q) :
    LinearMap.trace R B TB = LinearMap.trace R A TA + LinearMap.trace R C TC := by
  let e : A ≃ₗ[R] LinearMap.ker q :=
    (LinearEquiv.ofInjective i hi).trans (LinearEquiv.ofEq _ _ hex)
  have he (x : A) : (e x).1 = i x := rfl
  have hqker : ∀ z ∈ LinearMap.ker q, TB z ∈ LinearMap.ker q := by
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    have h := LinearMap.congr_fun hright z
    simpa only [LinearMap.comp_apply, hz, map_zero] using h
  have hconj : TB.restrict hqker = e.conj TA := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change TB z.1 = (e (TA (e.symm z))).1
    rw [he]
    have h := LinearMap.congr_fun hleft (e.symm z)
    simp only [LinearMap.comp_apply] at h
    rw [← he, e.apply_symm_apply] at h
    exact h
  have h := hg2_trace_surjective q hq TB TC hright
  change LinearMap.trace R B TB = LinearMap.trace R _ (TB.restrict hqker) + _ at h
  rw [hconj, LinearMap.trace_conj'] at h
  exact h

theorem hg2_trace_submodule {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (p : Submodule R M) [Module.Free R p] [Module.Finite R p]
    [Module.Free R (M ⧸ p)] [Module.Finite R (M ⧸ p)]
    (T : Module.End R M) (hp : ∀ z ∈ p, T z ∈ p) :
    LinearMap.trace R M T = LinearMap.trace R p (T.restrict hp) +
      LinearMap.trace R (M ⧸ p) (p.mapQ p T hp) := by
  letI : Module.Free R (LinearMap.ker p.mkQ) := by rw [Submodule.ker_mkQ]; infer_instance
  letI : Module.Finite R (LinearMap.ker p.mkQ) := by rw [Submodule.ker_mkQ]; infer_instance
  apply hg2_trace_exact p.subtype p.mkQ p.subtype_injective p.mkQ_surjective (by rw [Submodule.range_subtype, Submodule.ker_mkQ])
  · rfl
  · apply LinearMap.ext
    intro z
    rfl

theorem hg2_projectorCoeff_conjugacy_sum (k : b4b_Group) :
    (∑ x : b4b_Group, (b4b_projectorCoeff (x * k * x⁻¹) : ℂ)) =
      (b4b_projectorDenominator : ℂ) *
        ((b4b_toMatrix k).trace + star ((b4b_toMatrix k).trace)) := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0)
    (b63l_average_scalar (b4b_toMatrix k))
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  simp only [b63l_projectorCoeff_complex, map_mul, mul_add, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← map_sum]
  rw [h]
  norm_num [b4b_projectorDenominator, map_mul]
  simp only [map_ofNat]
  ring

theorem hg2_coset_stabilizer_sum {G R : Type*} [Group G] [Fintype G] [CommRing R]
    (H : Subgroup G) (F : G → R) (x : G) :
    (∑ h : G, if h • (x : G ⧸ H) = (x : G ⧸ H) then F h else 0) =
      ∑ k : H, F (x * k.1 * x⁻¹) := by
  classical
  let e : H ≃ {h : G // h • (x : G ⧸ H) = (x : G ⧸ H)} :=
    { toFun := fun k => ⟨x * k.1 * x⁻¹, by
        change (((x * k.1 * x⁻¹) * x : G) : G ⧸ H) = (x : G ⧸ H)
        apply QuotientGroup.eq.mpr
        simpa [mul_assoc] using H.inv_mem k.2⟩
      invFun := fun h => ⟨x⁻¹ * h.1 * x, by
        have hh : ((h.1 * x : G) : G ⧸ H) = (x : G ⧸ H) := h.2
        simpa only [mul_assoc] using QuotientGroup.eq.mp hh.symm⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc]) }
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun h : G => h • (x : G ⧸ H) = (x : G ⧸ H)) (Finset.univ.filter (fun h : G => h • (x : G ⧸ H) = (x : G ⧸ H))) (by intro h; exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ h))) F]
  exact (Fintype.sum_equiv e (fun k => F (x * k.1 * x⁻¹)) (fun h => F h.1)
    (fun k => rfl)).symm

theorem hg2_coset_class_sum {G R : Type*} [Group G] [Fintype G] [CommRing R]
    (H : Subgroup G) (F : G → R) (hF : ∀ x k, F (x * k * x⁻¹) = F k) :
    (∑ h : G, F h * ∑ q : G ⧸ H, if h • q = q then (1 : R) else 0) =
      Fintype.card (G ⧸ H) * ∑ k : H, F k.1 := by
  classical
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  have hq (q : G ⧸ H) :
      (∑ h : G, if h • q = q then F h else 0) = ∑ k : H, F k.1 := by
    induction q using QuotientGroup.induction_on with
    | H x => rw [hg2_coset_stabilizer_sum]; simp only [hF]
  simp only [hq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]

theorem hg2_weighted_class_sum {G R : Type*} [Group G] [Fintype G] [CommRing R]
    (a F : G → R) (hF : ∀ x k, F (x * k * x⁻¹) = F k) :
    (∑ h : G, (∑ x : G, a (x * h * x⁻¹)) * F h) =
      Fintype.card G * ∑ h : G, a h * F h := by
  classical
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hx (x : G) : (∑ h : G, a (x * h * x⁻¹) * F h) = ∑ h : G, a h * F h := by
    let e : G ≃ G := (Equiv.mulLeft x).trans (Equiv.mulRight x⁻¹)
    exact Fintype.sum_equiv e _ _ (fun h => by simp [e, hF])
  simp only [hx, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
theorem hg2_cyclic_character_sum (g : b4b_Group) :
    (∑ k : Subgroup.zpowers g, (b4b_toMatrix k.1).trace) =
      (Nat.card (Subgroup.zpowers g) : ℂ) *
        (4 - ((b4b_toMatrix g - 1).rank : ℂ)) := by
  classical
  let H := Subgroup.zpowers g
  let ρ : Representation ℂ H (Fin 4 → ℂ) := b63d_naturalRep.comp H.subtype
  let γ : H := ⟨g, Subgroup.mem_zpowers g⟩
  have hgen (x : H) : x ∈ Subgroup.zpowers γ := by
    obtain ⟨n, hn⟩ := x.2
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact hn
  have hinv : ρ.invariants = LinearMap.ker (b63d_naturalRep g - 1) := by
    ext v
    rw [Representation.mem_invariants_iff_of_forall_mem_zpowers ρ γ hgen v,
      LinearMap.mem_ker]
    change b63d_naturalRep g v = v ↔ b63d_naturalRep g v - v = 0
    exact sub_eq_zero.symm
  letI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := H)).ne')
  have h := Representation.card_inv_mul_sum_char_eq_finrank ρ
  have hc (k : H) : ρ.character k = (b4b_toMatrix k.1).trace := by
    change LinearMap.trace ℂ (Fin 4 → ℂ) (Matrix.toLin' (b4b_toMatrix k.1)) = _
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 4))]
    simp
  simp only [hc] at h
  rw [hinv] at h
  have hr := LinearMap.finrank_range_add_finrank_ker (b63d_naturalRep g - 1)
  have hrank : Module.finrank ℂ (LinearMap.range (b63d_naturalRep g - 1)) =
      (b4b_toMatrix g - 1).rank := by
    have hm : b63d_naturalRep g - 1 = Matrix.toLin' (b4b_toMatrix g - 1) := by
      rw [map_sub, Matrix.toLin'_one]
      rfl
    rw [hm]
    rfl
  rw [hrank] at hr
  have hd : Module.finrank ℂ (Fin 4 → ℂ) = 4 := by simp
  rw [hd] at hr
  have hcard : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hh : (∑ k : H, (b4b_toMatrix k.1).trace) =
      (Nat.card H : ℂ) * Module.finrank ℂ (LinearMap.ker (b63d_naturalRep g - 1)) := by
    calc
      _ = (Nat.card H : ℂ) * ((Nat.card H : ℂ)⁻¹ * ∑ k : H, (b4b_toMatrix k.1).trace) := by
        rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
      _ = _ := by rw [h]
  rw [hh]
  congr 1
  have hr' : ((b4b_toMatrix g - 1).rank : ℂ) +
      (Module.finrank ℂ (LinearMap.ker (b63d_naturalRep g - 1)) : ℂ) = 4 := by
    exact_mod_cast hr
  linear_combination hr'

theorem hg2_fixed_coset_conj {G R : Type*} [Group G] [Fintype G] [CommRing R]
    (H : Subgroup G) (x k : G) :
    (∑ q : G ⧸ H, if (x * k * x⁻¹) • q = q then (1 : R) else 0) =
      ∑ q : G ⧸ H, if k • q = q then (1 : R) else 0 := by
  classical
  let e : (G ⧸ H) ≃ (G ⧸ H) :=
    { toFun := fun q => x • q
      invFun := fun q => x⁻¹ • q
      left_inv := fun q => inv_smul_smul x q
      right_inv := fun q => smul_inv_smul x q }
  exact (Fintype.sum_equiv e _ _ (fun q => by simp [e, mul_smul])).symm

theorem hg2_projector_coset_trace (g : b4b_Group) :
    (∑ h : b4b_Group, (b4b_projectorCoeff h : ℂ) *
      ∑ q : b4b_Group ⧸ Subgroup.zpowers g, if h • q = q then (1 : ℂ) else 0) =
      (b4b_projectorDenominator : ℂ) * (8 - 2 * ((b4b_toMatrix g - 1).rank : ℂ)) := by
  classical
  let H := Subgroup.zpowers g
  let F : b4b_Group → ℂ := fun h => ∑ q : b4b_Group ⧸ H, if h • q = q then 1 else 0
  let χ : b4b_Group → ℂ := fun h => (b4b_toMatrix h).trace + star ((b4b_toMatrix h).trace)
  have hχ : ∀ x k, χ (x * k * x⁻¹) = χ k := by
    intro x k
    have ht : (b4b_toMatrix (x * k * x⁻¹)).trace = (b4b_toMatrix k).trace := by
      rw [map_mul, map_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← map_mul,
        inv_mul_cancel, map_one, Matrix.one_mul]
    simp only [χ, ht]
  have havg := hg2_weighted_class_sum (fun h : b4b_Group => (b4b_projectorCoeff h : ℂ)) F
    (hg2_fixed_coset_conj H)
  have hchar : (∑ k : H, χ k.1) = (Nat.card H : ℂ) *
      (8 - 2 * ((b4b_toMatrix g - 1).rank : ℂ)) := by
    simp only [χ, Finset.sum_add_distrib]
    change (∑ k : H, (b4b_toMatrix k.1).trace) +
      (∑ k : H, starRingEnd ℂ ((b4b_toMatrix k.1).trace)) = _
    rw [← map_sum]
    rw [hg2_cyclic_character_sum g]
    simp only [map_mul, map_sub, map_ofNat, map_natCast]
    ring
  have hcard : (Fintype.card b4b_Group : ℂ) =
      (Fintype.card (b4b_Group ⧸ H) : ℂ) * (Nat.card H : ℂ) := by
    have h := Fintype.card_congr (Subgroup.groupEquivQuotientProdSubgroup (s := H))
    simpa only [Fintype.card_prod, Nat.card_eq_fintype_card, Nat.cast_mul] using
      congrArg (Nat.cast : ℕ → ℂ) h
  have hnonzero : (Fintype.card b4b_Group : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hnonzero
  change (Fintype.card b4b_Group : ℂ) * (∑ h : b4b_Group, (b4b_projectorCoeff h : ℂ) * F h) = _
  rw [← havg]
  simp_rw [hg2_projectorCoeff_conjugacy_sum]
  change (∑ h : b4b_Group, ((b4b_projectorDenominator : ℂ) * χ h) * F h) = _
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [hg2_coset_class_sum H χ hχ, hchar, hcard]
  ring

theorem hg2_projectorCoeff_sum : (∑ g : b4b_Group, b4b_projectorCoeff g) = 0 := by
  apply Int.cast_injective (α := ℂ)
  have hz : (∑ g : b4b_Group, b4b_toMatrix g 0 0) = 0 := by
    have h := Equiv.sum_comp (Equiv.mulLeft b63d_scalarElement)
      (fun g : b4b_Group => b4b_toMatrix g 0 0)
    change (∑ g : b4b_Group, b4b_toMatrix (b63d_scalarElement * g) 0 0) =
      ∑ g : b4b_Group, b4b_toMatrix g 0 0 at h
    simp only [map_mul, b63d_scalarElement_matrix, Matrix.smul_mul,
      Matrix.one_mul, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h
    have hh : (g32h_omega - 1) * (∑ g : b4b_Group, b4b_toMatrix g 0 0) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr b63d_omega_ne_one)
  push_cast
  simp only [b63l_projectorCoeff_complex, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← map_sum, hz, map_zero, mul_zero, add_zero]

set_option backward.isDefEq.respectTransparency false in
theorem hg2_trace_complex {R A B C H : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup A] [Module R A] [Module.Free R A] [Module.Finite R A]
    [AddCommGroup B] [Module R B] [Module.Free R B] [Module.Finite R B]
    [AddCommGroup C] [Module R C] [Module.Free R C] [Module.Finite R C]
    [AddCommGroup H] [Module R H] [Module.Free R H] [Module.Finite R H]
    (b₂ : A →ₗ[R] B) (b₁ : B →ₗ[R] C) (hb : b₁ ∘ₗ b₂ = 0)
    (a : C →ₗ[R] R) (ha : Function.Surjective a) (hex : LinearMap.range b₁ = LinearMap.ker a)
    (Q : LinearMap.ker b₁ →ₗ[R] H) (hQ : Function.Surjective Q)
    (hker : LinearMap.ker Q = (LinearMap.range b₂).comap (LinearMap.ker b₁).subtype)
    (T₂ : Module.End R A) (T₁ : Module.End R B) (T₀ : Module.End R C) (TH : Module.End R H)
    (hc₂ : b₂ ∘ₗ T₂ = T₁ ∘ₗ b₂) (hc₁ : b₁ ∘ₗ T₁ = T₀ ∘ₗ b₁)
    (hc₀ : a ∘ₗ T₀ = 0) (hz₂ : ∀ z ∈ LinearMap.ker b₂, T₂ z = 0)
    (hcH : ∀ (z : LinearMap.ker b₁) (hz : T₁ z.1 ∈ LinearMap.ker b₁),
      Q ⟨T₁ z.1, hz⟩ = TH (Q z)) :
    LinearMap.trace R H TH + LinearMap.trace R C T₀ + LinearMap.trace R A T₂ =
      LinearMap.trace R B T₁ := by
  have hz₁ : ∀ z ∈ LinearMap.ker b₁, T₁ z ∈ LinearMap.ker b₁ := by
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    have h := LinearMap.congr_fun hc₁ z
    simpa only [LinearMap.comp_apply, hz, map_zero] using h
  have hi₀ : ∀ z ∈ LinearMap.range b₁, T₀ z ∈ LinearMap.range b₁ := by
    rintro z ⟨w, rfl⟩
    exact ⟨T₁ w, LinearMap.congr_fun hc₁ w⟩
  have hi₁ : ∀ z ∈ LinearMap.range b₂, T₁ z ∈ LinearMap.range b₂ := by
    rintro z ⟨w, rfl⟩
    exact ⟨T₂ w, LinearMap.congr_fun hc₂ w⟩
  let Z := T₁.restrict hz₁
  let I₀ := T₀.restrict hi₀
  let I₁ := T₁.restrict hi₁
  have ht₁ := hg2_trace_exact (LinearMap.ker b₁).subtype b₁.rangeRestrict
    (Submodule.subtype_injective _) (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict b₁))
    (by rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict]) Z T₁ I₀ (by rfl) (by
      apply LinearMap.ext; intro z; apply Subtype.ext; exact LinearMap.congr_fun hc₁ z)
  have ht₀ := hg2_trace_exact (LinearMap.range b₁).subtype a
    (Submodule.subtype_injective _) ha (by rw [Submodule.range_subtype]; exact hex)
    I₀ T₀ 0 (by rfl) (by simpa using hc₀)
  have ht₂ := hg2_trace_exact (LinearMap.ker b₂).subtype b₂.rangeRestrict
    (Submodule.subtype_injective _) (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict b₂))
    (by rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict]) 0 T₂ I₁ (by
      apply LinearMap.ext; intro z; exact hz₂ z.1 z.2) (by
      apply LinearMap.ext; intro z; apply Subtype.ext; exact LinearMap.congr_fun hc₂ z)
  have hincl : LinearMap.range b₂ ≤ LinearMap.ker b₁ := LinearMap.range_le_ker_iff.mpr hb
  have htH := hg2_trace_exact (Submodule.inclusion hincl) Q
    (Submodule.inclusion_injective hincl) hQ
    (by rw [Submodule.range_inclusion]; exact hker.symm) I₁ Z TH (by rfl) (by
      apply LinearMap.ext; intro z; exact hcH z _)
  simp only [map_zero, zero_add, add_zero] at ht₀ ht₂
  linear_combination ht₀ + ht₂ - ht₁ - htH

end HodgeLean.Foundations.Program
