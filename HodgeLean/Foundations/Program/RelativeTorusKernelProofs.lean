import HodgeLean.Foundations.Program.RelativeTorusAlg
import HodgeLean.Foundations.Program.RelativeTorusKernelDefs
import HodgeLean.Foundations.Program.RelativeTorusTopology
import HodgeLean.Foundations.Program.RelativeTorusTotalSpace

set_option maxHeartbeats 400000

/-! # Track B2, families of complex tori and images of integral endomorphisms: proofs

One `_aux` theorem per statement of the frozen `RelativeTorusKernel.lean`; the bodies are open.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory Manifold
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program

section Fibre

variable {Λ : Type*} [AddCommGroup Λ]

theorem b2_two_mul_finrank_aux [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    2 * Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F) = Module.finrank ℤ Λ := by
  have h1 := Submodule.finrank_quotient_add_finrank F
  have h2 := Submodule.finrank_add_eq_of_isCompl hF
  have h3 := b2a_finrank_conjSubmodule F
  have h4 : Module.finrank ℂ (ℂ ⊗[ℤ] Λ) = Module.finrank ℤ Λ := Module.finrank_baseChange
  omega

theorem b2_latticeMap_basis_aux {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ Λ)
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    ∃ c : Module.Basis ι ℝ ((ℂ ⊗[ℤ] Λ) ⧸ F), ∀ i, c i = b2_latticeMap Λ F (b i) := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  have hli : LinearIndependent ℝ (fun i ↦ b2_latticeMap Λ F (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    set w : ℂ ⊗[ℤ] Λ := ∑ j, ((g j : ℂ) ⊗ₜ[ℤ] b j) with hw
    have hmk : Submodule.Quotient.mk (p := F) w = 0 := by
      rw [← hg, hw, ← Submodule.mkQ_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Submodule.mkQ_apply, b2_latticeMap, AddMonoidHom.coe_comp, Function.comp_apply,
        LinearMap.toAddMonoidHom_coe, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul]
      congr 1
      change _ = g j • ((1 : ℂ) ⊗ₜ[ℤ] b j)
      rw [TensorProduct.smul_tmul', Complex.real_smul, mul_one]
    have hwF : w ∈ F := (Submodule.Quotient.mk_eq_zero F).1 hmk
    have hconj : b2_conj Λ w = w := by
      rw [hw, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [b2a_conj_tmul, Complex.conj_ofReal]
    have hw0 := b2a_eq_zero_of_mem_of_conj hF hwF hconj
    have := congrArg (fun v ↦ (b.baseChange ℂ).repr v i) hw0
    simp only [hw, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
      Module.Basis.baseChange_repr_tmul, Module.Basis.repr_self, map_zero,
      Finsupp.coe_zero, Pi.zero_apply] at this
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [Finsupp.single_eq_of_ne hj.symm, zero_smul])
      (fun h ↦ absurd (Finset.mem_univ i) h), Finsupp.single_eq_same, one_smul] at this
    exact_mod_cast this
  have hcard : Fintype.card ι = Module.finrank ℝ ((ℂ ⊗[ℤ] Λ) ⧸ F) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, b2_two_mul_finrank_aux F hF,
      Module.finrank_eq_card_basis b]
  have : FiniteDimensional ℝ ((ℂ ⊗[ℤ] Λ) ⧸ F) := Module.Finite.trans ℂ _
  exact ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli hcard, fun i ↦ by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']⟩

theorem b2_torus_addEquiv_aux {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ Λ)
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    ∃ φ : b2_torus Λ F ≃ₜ+ (ι → UnitAddCircle), ∀ t : ι → ℝ,
      φ (QuotientAddGroup.mk (∑ i, t i • b2_latticeMap Λ F (b i))) =
        fun i ↦ (t i : UnitAddCircle) := by
  obtain ⟨c, hc⟩ := b2_latticeMap_basis_aux b F hF
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  have : T2Space ((ℂ ⊗[ℤ] Λ) ⧸ F) := (b2_coordHomeomorph Λ F).isEmbedding.t2Space
  have : ContinuousSMul ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F) := inferInstance
  have : ContinuousSMul ℝ ((ℂ ⊗[ℤ] Λ) ⧸ F) := by
    refine ⟨?_⟩
    have : (fun p : ℝ × ((ℂ ⊗[ℤ] Λ) ⧸ F) ↦ p.1 • p.2) =
        fun p ↦ ((p.1 : ℂ) • p.2) := funext fun p ↦ (Complex.coe_smul p.1 p.2).symm
    rw [this]
    exact (Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd
  have : FiniteDimensional ℝ ((ℂ ⊗[ℤ] Λ) ⧸ F) := Module.Finite.trans ℂ _
  let ψ : ((ℂ ⊗[ℤ] Λ) ⧸ F) ≃ₜ (ι → ℝ) :=
    { toEquiv := c.equivFun.toEquiv
      continuous_toFun := LinearMap.continuous_of_finiteDimensional c.equivFun.toLinearMap
      continuous_invFun :=
        LinearMap.continuous_of_finiteDimensional c.equivFun.symm.toLinearMap }
  have hψ : ∀ v, ψ v = c.equivFun v := fun _ ↦ rfl
  have hlat : ∀ x : Λ, c.equivFun (b2_latticeMap Λ F x) = fun i ↦ (b.repr x i : ℝ) := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    have : ∑ i, b2_latticeMap Λ F (b.repr x i • b i) =
        c.equivFun.symm (fun i ↦ (b.repr x i : ℝ)) := by
      rw [Module.Basis.equivFun_symm_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_zsmul, ← hc, Int.cast_smul_eq_zsmul]
    rw [this, LinearEquiv.apply_symm_apply]
  let Φ : ((ℂ ⊗[ℤ] Λ) ⧸ F) →+ (ι → UnitAddCircle) :=
    { toFun := fun v i ↦ ((c.equivFun v i : ℝ) : UnitAddCircle)
      map_zero' := by ext i; simp
      map_add' := fun v w ↦ by ext i; simp }
  have hΦ : ∀ v, Φ v = fun i ↦ ((c.equivFun v i : ℝ) : UnitAddCircle) := fun _ ↦ rfl
  have hΦc : Continuous Φ :=
    continuous_pi fun i ↦ (AddCircle.continuous_mk' 1).comp
      ((continuous_apply i).comp ψ.continuous)
  have hΦo : IsOpenMap Φ := by
    have h1 : IsOpenMap (Pi.map fun _ : ι ↦ (QuotientAddGroup.mk : ℝ → UnitAddCircle)) :=
      IsOpenMap.piMap (fun _ ↦ QuotientAddGroup.isOpenMap_coe)
        (Filter.Eventually.of_forall fun _ ↦ QuotientAddGroup.mk_surjective)
    exact h1.comp ψ.isOpenMap
  have hΦs : Function.Surjective Φ := by
    intro y
    choose x hx using fun i ↦ QuotientAddGroup.mk_surjective (y i)
    refine ⟨c.equivFun.symm x, ?_⟩
    ext i
    rw [hΦ, LinearEquiv.apply_symm_apply]
    exact hx i
  have hker : (b2_latticeMap Λ F).range = Φ.ker := by
    ext v
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      ext i
      rw [hΦ, hlat]
      exact (AddCircle.coe_eq_zero_iff 1).2 ⟨b.repr x i, by simp⟩
    · intro hv
      have h : ∀ i, ∃ n : ℤ, n • (1 : ℝ) = c.equivFun v i := fun i ↦
        (AddCircle.coe_eq_zero_iff 1).1 (congrFun hv i)
      choose n hn using h
      refine ⟨b.equivFun.symm n, c.equivFun.injective ?_⟩
      rw [hlat]
      ext i
      rw [← hn i, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, zsmul_one]
  let e := QuotientAddGroup.liftEquiv (b2_latticeMap Λ F).range hΦs hker
  have hec : Continuous e :=
    (QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff).mp hΦc
  have heo : IsOpenMap e := by
    intro U hU
    have : e '' U = Φ '' (QuotientAddGroup.mk ⁻¹' U) := by
      conv_lhs => rw [← Set.image_preimage_eq U QuotientAddGroup.mk_surjective]
      rw [← Set.image_comp]
      rfl
    rw [this]
    exact hΦo _ (hU.preimage QuotientAddGroup.continuous_mk)
  refine ⟨{ e with
    continuous_toFun := hec
    continuous_invFun :=
      (e.toEquiv.toHomeomorphOfContinuousOpen hec heo).symm.continuous },
    fun t ↦ ?_⟩
  change Φ _ = _
  rw [hΦ]
  ext i
  congr 1
  have : ∑ i, t i • b2_latticeMap Λ F (b i) = c.equivFun.symm t := by
    rw [Module.Basis.equivFun_symm_apply]
    simp only [hc]
  rw [this, LinearEquiv.apply_symm_apply]

theorem b2_riemannForm_nondegenerate_aux [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    (Q : LinearMap.BilinForm ℤ Λ) (hF : b2_IsWeightOne Λ F) (hQ : b2_IsRiemannForm Λ F Q)
    (x : Λ) (hx : ∀ y, Q x y = 0) : x = 0 := by
  have hmem : (1 : ℂ) ⊗ₜ[ℤ] x ∈ F ⊔ b2_conjSubmodule Λ F := hF.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨f, hf, g, hg, hfg⟩ := Submodule.mem_sup.1 hmem
  have hc : b2_conj Λ f + b2_conj Λ g = f + g := by rw [← map_add, hfg, b2a_conj_incl]
  have h1 : f - b2_conj Λ g ∈ F := sub_mem hf (b2a_conj_mem_of_mem_conjSubmodule hg)
  have h2 : f - b2_conj Λ g ∈ b2_conjSubmodule Λ F := by
    have : f - b2_conj Λ g = b2_conj Λ f - g := by
      rw [sub_eq_sub_iff_add_eq_add, hc]
    rw [this]
    exact sub_mem (b2a_conj_mem_conjSubmodule hf) hg
  have h3 : f - b2_conj Λ g = 0 := by
    have := hF.inf_eq_bot ▸ (Submodule.mem_inf.2 ⟨h1, h2⟩)
    exact (Submodule.mem_bot ℂ).1 this
  have hg' : g = b2_conj Λ f := by
    rw [sub_eq_zero] at h3
    rw [h3, b2a_conj_conj]
  have hzero : Q.baseChange ℂ f (b2_conj Λ f) = 0 := by
    have := b2a_baseChange_incl_left Q x hx (b2_conj Λ f)
    rw [← hfg, hg', map_add, LinearMap.add_apply, b2a_baseChange_alt Q hQ.alt, add_zero] at this
    exact this
  have hf0 : f = 0 := by
    by_contra hne
    have := hQ.positive f hf hne
    rw [hzero, mul_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  have : (1 : ℂ) ⊗ₜ[ℤ] x = (1 : ℂ) ⊗ₜ[ℤ] (0 : Λ) := by
    rw [← hfg, hg', hf0, map_zero, add_zero, TensorProduct.tmul_zero]
  exact b2a_incl_injective this

theorem b2_image_isWeightOne_aux (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (f : Λ →+ Λ) (hf : F ≤ F.comap (b2_cplxMap f)) :
    b2_IsWeightOne f.range (b2_imageF F f) := by
  have hι := b2a_cplxMap_subtype_injective f.range
  have himg : ∀ a ∈ F, b2_cplxMap f.rangeRestrict a ∈ b2_imageF F f := fun a ha ↦ by
    change b2_cplxMap f.range.subtype _ ∈ F
    rw [b2a_cplxMap_rangeRestrict]
    exact hf ha
  constructor
  · rw [Submodule.disjoint_def]
    intro w hw hw'
    obtain ⟨a, ha, rfl⟩ := b2a_mem_conjSubmodule.1 hw'
    have h1 : b2_cplxMap f.range.subtype (b2_conj _ a) ∈ F := hw
    have h2 : b2_cplxMap f.range.subtype (b2_conj _ a) ∈ b2_conjSubmodule Λ F := by
      rw [← b2a_conj_cplxMap]
      exact b2a_conj_mem_conjSubmodule ha
    have := hF.inf_eq_bot ▸ (Submodule.mem_inf.2 ⟨h1, h2⟩)
    exact hι (((Submodule.mem_bot ℂ).1 this).trans (map_zero _).symm)
  · rw [codisjoint_iff, eq_top_iff]
    intro w _
    obtain ⟨u, rfl⟩ := b2a_cplxMap_rangeRestrict_surjective f w
    have hmem : u ∈ F ⊔ b2_conjSubmodule Λ F := hF.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hmem
    obtain ⟨a', ha', rfl⟩ := b2a_mem_conjSubmodule.1 hb
    rw [map_add]
    refine Submodule.add_mem_sup (himg a ha) ?_
    rw [← b2a_conj_cplxMap]
    exact b2a_conj_mem_conjSubmodule (himg a' ha')

theorem b2_image_isRiemannForm_aux (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (Q : LinearMap.BilinForm ℤ Λ)
    (hQ : b2_IsRiemannForm Λ F Q) (f : Λ →+ Λ) :
    b2_IsRiemannForm f.range (b2_imageF F f) (b2_imageQ Q f) := by
  have hι := b2a_cplxMap_subtype_injective f.range
  have hb : ∀ u v, (b2_imageQ Q f).baseChange ℂ u v =
      Q.baseChange ℂ (b2_cplxMap f.range.subtype u) (b2_cplxMap f.range.subtype v) :=
    b2a_baseChange_compl Q f.range.subtype
  refine ⟨fun x ↦ hQ.alt _, fun x hx y hy ↦ ?_, fun x hx hne ↦ ?_⟩
  · rw [hb]
    exact hQ.isotropic _ hx _ hy
  · rw [hb, ← b2a_conj_cplxMap]
    refine hQ.positive _ hx fun h ↦ hne (hι (h.trans (map_zero _).symm))

theorem b2_subTorus_range_aux (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (f : Λ →+ Λ)
    (hf : F ≤ F.comap (b2_cplxMap f)) :
    (b2_subTorus F f).range = (b2_torusHom F F f hf).range := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective s
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨u, rfl⟩ := b2a_cplxMap_rangeRestrict_surjective f w
    refine ⟨QuotientAddGroup.mk (Submodule.Quotient.mk u), ?_⟩
    change QuotientAddGroup.mk (Submodule.Quotient.mk (b2_cplxMap f u)) =
      QuotientAddGroup.mk (Submodule.Quotient.mk (b2_cplxMap f.range.subtype _))
    rw [b2a_cplxMap_rangeRestrict]
  · rintro ⟨s, rfl⟩
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective s
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨QuotientAddGroup.mk (Submodule.Quotient.mk (b2_cplxMap f.rangeRestrict u)), ?_⟩
    change QuotientAddGroup.mk (Submodule.Quotient.mk (b2_cplxMap f.range.subtype _)) =
      QuotientAddGroup.mk (Submodule.Quotient.mk (b2_cplxMap f u))
    rw [b2a_cplxMap_rangeRestrict]

theorem b2_subTorus_injective_aux (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (e : Λ →+ Λ)
    (he : e.comp e = e) (hf : F ≤ F.comap (b2_cplxMap e)) :
    Function.Injective (b2_subTorus F e) := by
  refine (injective_iff_map_eq_zero _).2 fun t ht ↦ ?_
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨x, hx⟩ := (b2a_torus_mk_eq_zero_iff F _).1 ht
  refine b2a_subTorus_mk_eq_zero F e w x ?_
  have := hf hx
  rwa [Submodule.mem_comap, map_sub, b2a_cplxMap_idem_subtype e he] at this

theorem b2_torus_split_aux (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (e : Λ →+ Λ)
    (he : e.comp e = e) (hf : F ≤ F.comap (b2_cplxMap e)) :
    Function.Bijective (fun p : b2_torus e.range (b2_imageF F e) ×
        b2_torus (AddMonoidHom.id Λ - e).range (b2_imageF F (AddMonoidHom.id Λ - e)) ↦
      b2_subTorus F e p.1 + b2_subTorus F (AddMonoidHom.id Λ - e) p.2) := by
  set e' := AddMonoidHom.id Λ - e with he'_def
  have he' : e'.comp e' = e' := b2a_idem_one_sub e he
  have hf' : F ≤ F.comap (b2_cplxMap e') := fun x hx ↦ by
    rw [Submodule.mem_comap, he'_def, b2a_cplxMap_id_sub_apply]
    exact sub_mem hx (hf hx)
  have hfun : (fun p : b2_torus e.range (b2_imageF F e) × b2_torus e'.range (b2_imageF F e') ↦
      b2_subTorus F e p.1 + b2_subTorus F e' p.2) =
      ((b2_subTorus F e).coprod (b2_subTorus F e') : _ →+ b2_torus Λ F) := rfl
  rw [hfun]
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun ⟨a, b⟩ hab ↦ ?_
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨q', rfl⟩ := QuotientAddGroup.mk_surjective b
    obtain ⟨w', rfl⟩ := Submodule.Quotient.mk_surjective _ q'
    have hab' : (QuotientAddGroup.mk (Submodule.Quotient.mk (b2_cplxMap e.range.subtype w +
        b2_cplxMap e'.range.subtype w')) : b2_torus Λ F) = 0 := hab
    obtain ⟨x, hx⟩ := (b2a_torus_mk_eq_zero_iff F _).1 hab'
    have h1 := hf hx
    have h2 := hf' hx
    rw [Submodule.mem_comap, map_sub, map_add, b2a_cplxMap_idem_subtype e he,
      b2a_cplxMap_idem_one_sub_subtype e he, add_zero] at h1
    rw [Submodule.mem_comap, map_sub, map_add, b2a_cplxMap_idem_subtype e' he'] at h2
    have h3 : b2_cplxMap e' (b2_cplxMap e.range.subtype w) = 0 := by
      rw [he'_def, b2a_cplxMap_id_sub_apply, b2a_cplxMap_idem_subtype e he, sub_self]
    rw [h3, zero_add] at h2
    rw [Prod.mk_eq_zero]
    exact ⟨b2a_subTorus_mk_eq_zero F e w x h1, b2a_subTorus_mk_eq_zero F e' w' x h2⟩
  · intro t
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective t
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨(QuotientAddGroup.mk (Submodule.Quotient.mk (b2_cplxMap e.rangeRestrict v)),
      QuotientAddGroup.mk (Submodule.Quotient.mk (b2_cplxMap e'.rangeRestrict v))), ?_⟩
    change (QuotientAddGroup.mk (Submodule.Quotient.mk
      (b2_cplxMap e.range.subtype (b2_cplxMap e.rangeRestrict v) +
        b2_cplxMap e'.range.subtype (b2_cplxMap e'.rangeRestrict v))) : b2_torus Λ F) = _
    rw [b2a_cplxMap_rangeRestrict, b2a_cplxMap_rangeRestrict, he'_def,
      b2a_cplxMap_id_sub_apply, add_sub_cancel]

theorem b2_one_sub_le_comap_aux (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (e : Λ →+ Λ)
    (hf : F ≤ F.comap (b2_cplxMap e)) :
    F ≤ F.comap (b2_cplxMap (AddMonoidHom.id Λ - e)) := by
  intro x hx
  rw [Submodule.mem_comap, b2a_cplxMap_id_sub_apply]
  exact sub_mem hx (hf hx)

theorem b2_latticeMap_discrete_aux [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    DiscreteTopology (b2_latticeMap Λ F).range := by
  set b := Module.Free.chooseBasis ℤ Λ
  obtain ⟨c, hc⟩ := b2_latticeMap_basis_aux b F hF
  -- the lattice lies in the `ℤ`-span of the real basis `c`
  have hspan : ∀ y ∈ (b2_latticeMap Λ F).range, y ∈ Submodule.span ℤ (Set.range c) := by
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [map_zsmul, ← hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- the coordinates of `c` are continuous
  have hcont : Continuous c.equivFun := by
    have h1 : Continuous (c.equivFun.toLinearMap ∘ₗ
        ((b2_coord ((ℂ ⊗[ℤ] Λ) ⧸ F)).symm.toLinearMap.restrictScalars ℝ)) :=
      LinearMap.continuous_of_finiteDimensional _
    have h2 := h1.comp (b2_coordHomeomorph Λ F).continuous
    convert h2 using 1
    ext v
    simp [b2_coordHomeomorph]
  have hmaps : Set.MapsTo c.equivFun ((b2_latticeMap Λ F).range : Set _)
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ Λ))) :
        Set _) := by
    intro y hy
    have := hspan y hy
    rw [Module.Basis.mem_span_iff_repr_mem] at this
    rw [SetLike.mem_coe, Module.Basis.mem_span_iff_repr_mem]
    simpa using this
  have : DiscreteTopology ((Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ Λ))) :
        Set (Module.Free.ChooseBasisIndex ℤ Λ → ℝ))) :=
    inferInstanceAs (DiscreteTopology (Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ Λ)))))
  exact DiscreteTopology.of_continuous_injective (hcont.restrict hmaps)
    (Subtype.map_injective _ c.equivFun.injective)

theorem b2_torus_t2Space_aux [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    [DiscreteTopology (b2_latticeMap Λ F).range] :
    T2Space (b2_torus Λ F) :=
  b2t_torus_t2Space F

theorem b2_torus_compactSpace_aux [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    CompactSpace (b2_torus Λ F) := by
  obtain ⟨φ, -⟩ := b2_torus_addEquiv_aux (Module.Free.chooseBasis ℤ Λ) F hF
  exact φ.toHomeomorph.symm.compactSpace

theorem b2_torus_isManifold_aux [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    [DiscreteTopology (b2_latticeMap Λ F).range] :
    IsManifold 𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) ω (b2_torus Λ F) :=
  b2t_isManifold F

theorem b2_torusCover_isCoveringMap_aux [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    [DiscreteTopology (b2_latticeMap Λ F).range] :
    IsCoveringMap (b2_torusCover Λ F) :=
  b2t_torusCover_isCoveringMap F

theorem b2_torusCover_contMDiff_aux [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    [DiscreteTopology (b2_latticeMap Λ F).range] :
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) ω (b2_torusCover Λ F) :=
  b2t_torusCover_contMDiff F

end Fibre

section Holomorphic

variable {Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']

theorem b2_torusHom_contMDiff_aux [Module.Finite ℤ Λ'] [Module.Finite ℤ Λ]
    (F' : Submodule ℂ (ℂ ⊗[ℤ] Λ')) (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (g : Λ' →+ Λ)
    (hg : F' ≤ F.comap (b2_cplxMap g)) [DiscreteTopology (b2_latticeMap Λ' F').range]
    [DiscreteTopology (b2_latticeMap Λ F).range] :
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ') ⧸ F')) → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) ω (b2_torusHom F' F g hg) :=
  b2t_torusHom_contMDiff F' F g hg

end Holomorphic

section Family

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

theorem b2_image_flat_aux (L : b2_LatticeLocalSystem B)
    (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b))
    (hQ : ∀ (b b' : B) (γ : Path.Homotopic.Quotient b b') (x y : L.fiber b),
      Q b' (L.transport γ x) (L.transport γ y) = Q b x y)
    (e : L.functor ⟶ L.functor) :
    ∀ (b b' : B) (γ : Path.Homotopic.Quotient b b') (x y : (L.image e).fiber b),
      L.imageQ Q e b' ((L.image e).transport γ x) ((L.image e).transport γ y) =
        L.imageQ Q e b x y := by
  intro b b' γ x y
  exact hQ b b' γ (show L.imageObj e (FundamentalGroupoid.mk b) from x).1
    (show L.imageObj e (FundamentalGroupoid.mk b) from y).1

theorem b2_image_holomorphic_aux (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b))
    (hT : b2_IsPolarizedTorusFamily E L F Q) (e : L.functor ⟶ L.functor)
    (hf : ∀ b, F b ≤ (F b).comap (b2_cplxMap (e.app (FundamentalGroupoid.mk b)).hom)) :
    (L.image e).IsHolomorphicSubbundle E (L.imageF F e) :=
  b2f_image_holomorphic L F Q hT e hf

theorem b2_image_isPolarizedTorusFamily_aux (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b))
    (hT : b2_IsPolarizedTorusFamily E L F Q) (e : L.functor ⟶ L.functor)
    (hf : ∀ b, F b ≤ (F b).comap (b2_cplxMap (e.app (FundamentalGroupoid.mk b)).hom)) :
    b2_IsPolarizedTorusFamily E (L.image e) (L.imageF F e) (L.imageQ Q e) where
  holomorphic := b2_image_holomorphic_aux L F Q hT e hf
  flat := b2_image_flat_aux L Q hT.flat e
  hodge b := b2_image_isWeightOne_aux (F b) (hT.hodge b) _ (hf b)
  polarized b := b2_image_isRiemannForm_aux (F b) (Q b) (hT.polarized b) _

theorem b2_flatTriv_isOpenMap_aux (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (hhol : L.IsHolomorphicSubbundle E F)
    (hw : ∀ b, b2_IsWeightOne (L.fiber b) (F b)) (U : Set B) (hU : IsSimplyConnected U)
    (hUo : IsOpen U) (b₀ : U) :
    IsOpenMap (b2_flatTriv L F U hU b₀) ∧
      Set.range (b2_flatTriv L F U hU b₀) = b2_proj L F ⁻¹' U :=
  ⟨b2f_flatTriv_isOpenMap L F hhol U hU hUo b₀, b2f_flatTriv_range L F U hU b₀⟩

theorem b2_fiberIncl_isEmbedding_aux (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (hhol : L.IsHolomorphicSubbundle E F)
    (hw : ∀ b, b2_IsWeightOne (L.fiber b) (F b)) (b : B) :
    Topology.IsEmbedding (b2_fiberIncl L F b) :=
  b2f_fiberIncl_isEmbedding L F hhol b

theorem b2_totalSpace_complexManifold_aux [IsManifold 𝓘(ℂ, E) ω B]
    (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b))
    (hhol : L.IsHolomorphicSubbundle E F) (hw : ∀ b, b2_IsWeightOne (L.fiber b) (F b))
    (g : ℕ) (hg : ∀ b, Module.finrank ℤ (L.fiber b) = 2 * g) :
    ∃ cs : ChartedSpace (E × (Fin g → ℂ)) (b2_totalSpace L F),
      letI := cs
      IsManifold 𝓘(ℂ, E × (Fin g → ℂ)) ω (b2_totalSpace L F) ∧
      ContMDiff 𝓘(ℂ, E × (Fin g → ℂ)) 𝓘(ℂ, E) ω (b2_proj L F) ∧
      (∀ p, Function.Surjective (mfderiv 𝓘(ℂ, E × (Fin g → ℂ)) 𝓘(ℂ, E) (b2_proj L F) p)) ∧
      (∀ b, letI := b2_latticeMap_discrete_aux (F b) (hw b)
        ContMDiff 𝓘(ℂ, Fin (Module.finrank ℂ ((L.cFiber b) ⧸ F b)) → ℂ)
          𝓘(ℂ, E × (Fin g → ℂ)) ω (b2_fiberIncl L F b)) ∧
      ∀ (U : TopologicalSpace.Opens B) (hU : IsSimplyConnected (U : Set B)) (b₀ : U),
        ContMDiff (𝓘(ℂ, E).prod 𝓘(ℂ, Fin (Module.finrank ℂ (L.cFiber b₀)) → ℂ))
          𝓘(ℂ, E × (Fin g → ℂ)) ω
          (fun p : U × (Fin (Module.finrank ℂ (L.cFiber b₀)) → ℂ) ↦
            b2_flatTriv L F U hU b₀ (p.1, (b2_coord (L.cFiber b₀)).symm p.2)) := by
  have hfr : ∀ b, Nonempty (b2f_Frame E L F g b) :=
    b2f_frame_exists L F hhol g hg (fun b ↦ b2_two_mul_finrank_aux (F b) (hw b))
      (fun b β ↦ b2_latticeMap_basis_aux β (F b) (hw b))
  let fr := fun b ↦ (hfr b).some
  refine ⟨b2f_cs hhol fr, b2f_isManifold hhol fr, b2f_proj_contMDiff hhol fr,
    b2f_proj_mfderiv_surjective hhol fr, fun b ↦ ?_,
    fun U hU b₀ ↦ b2f_flatTriv_contMDiff hhol fr U hU b₀⟩
  let := b2_latticeMap_discrete_aux (F b) (hw b)
  have := b2_torus_isManifold_aux (F b)
  exact b2f_fiberIncl_contMDiff hhol fr b

end Family

section Standard

theorem b2_std_isWeightOne_aux : b2_IsWeightOne (Fin 2 → ℤ) b2_stdF := by
  rw [b2_IsWeightOne, b2_stdF, b2a_conjSubmodule_span_singleton]
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hx'
    have h := congrArg b2a_pi hb
    rw [map_smul, map_smul, b2a_stdVec_conj_pi, b2a_stdVec_pi] at h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul,
      mul_one] at h0 h1
    have ha : a = 0 := by
      have : (2 : ℂ) * a * Complex.I = 0 := by linear_combination (-1) * h1 + (-Complex.I) * h0
      simpa [Complex.I_ne_zero] using this
    rw [ha, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro w _
    set z := b2a_pi w
    refine Submodule.mem_sup.2 ⟨((z 0 - Complex.I * z 1) / 2) • b2a_stdVec,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
      ((z 0 + Complex.I * z 1) / 2) • b2_conj _ b2a_stdVec,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    apply b2a_pi.injective
    rw [map_add, map_smul, map_smul, b2a_stdVec_conj_pi, b2a_stdVec_pi]
    ext i; fin_cases i
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simp; ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simp
      linear_combination (-(z 1)) * Complex.I_sq

theorem b2_std_isRiemannForm_aux : b2_IsRiemannForm (Fin 2 → ℤ) b2_stdF b2_stdForm := by
  have halt : ∀ x, b2_stdForm x x = 0 := fun x ↦ by rw [b2a_stdForm_apply]; ring
  refine ⟨halt, fun x hx y hy ↦ ?_, fun x hx hne ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [map_smul, map_smul, LinearMap.smul_apply, b2a_baseChange_alt _ halt, smul_zero,
      smul_zero]
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have ha : a ≠ 0 := fun h ↦ hne (by rw [h, zero_smul])
    have hv : b2_stdForm.baseChange ℂ b2a_stdVec (b2_conj _ b2a_stdVec) = -2 * Complex.I := by
      rw [b2a_stdVec_conj]
      simp only [map_add, LinearMap.add_apply, LinearMap.BilinForm.baseChange_tmul,
        b2a_stdForm_apply]
      simp
      ring
    rw [b2a_conj_smul, map_smul, map_smul, LinearMap.smul_apply, hv, smul_eq_mul,
      smul_eq_mul]
    have : Complex.I * (starRingEnd ℂ a * (a * (-2 * Complex.I))) =
        2 * (a * starRingEnd ℂ a) := by
      linear_combination (-2 * a * starRingEnd ℂ a) * Complex.I_sq
    rw [this, Complex.mul_conj, show (2 : ℂ) * (Complex.normSq a : ℂ) =
      ((2 * Complex.normSq a : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    have := Complex.normSq_pos.2 ha
    linarith

theorem b2_const_isPolarizedTorusFamily_aux :
    b2_IsPolarizedTorusFamily ℂ (b2_constLocalSystem ℂ (Fin 2 → ℤ)) (fun _ ↦ b2_stdF)
      (fun _ ↦ b2_stdForm) := by
  refine ⟨fun b₁ ↦ ?_, fun b b' γ x y ↦ rfl, fun _ ↦ b2_std_isWeightOne_aux, fun _ ↦ b2_std_isRiemannForm_aux⟩
  have : ContractibleSpace (Set.univ : Set ℂ) := (Homeomorph.Set.univ ℂ).contractibleSpace
  have hU : IsSimplyConnected (Set.univ : Set ℂ) :=
    (inferInstance : SimplyConnectedSpace (Set.univ : Set ℂ))
  refine ⟨Set.univ, hU, Set.mem_univ _, isOpen_univ, 1, fun _ _ ↦ b2a_stdVec, fun _ ↦ ?_,
    fun b _ ↦ ?_⟩
  · have hc : (b2_constLocalSystem ℂ (Fin 2 → ℤ)).flatCoord Set.univ hU ⟨b₁, Set.mem_univ _⟩
        (fun _ ↦ b2a_stdVec) = fun _ ↦ b2a_stdVec := by
      funext b
      simp only [b2_LatticeLocalSystem.flatCoord, Set.mem_univ, dite_true]
      exact b2a_const_flatTransport _ _ _ _ _ _
    unfold b2_LatticeLocalSystem.IsHolomorphicSectionOn b2_IsHolomorphicOn
    rw [hc]
    exact contMDiffOn_const
  · show Submodule.span ℂ (Set.range fun _ : Fin 1 ↦ b2a_stdVec) = b2_stdF
    rw [Set.range_const]
    rfl

theorem b2_realF_not_isWeightOne_aux : ¬ b2_IsWeightOne (Fin 2 → ℤ) b2_realF := by
  intro h
  have h1 := b2a_incl_eq_zero_of_mem h (Submodule.mem_span_singleton_self _)
  rw [← TensorProduct.tmul_zero (R := ℤ) (Fin 2 → ℤ) (1 : ℂ)] at h1
  have := congrFun (b2a_incl_injective h1) 0
  simp at this

theorem b2_zero_not_isRiemannForm_aux {Λ : Type*} [AddCommGroup Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : F ≠ ⊥) : ¬ b2_IsRiemannForm Λ F 0 := by
  intro h
  obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hF
  have := h.positive x hx hne
  simp at this

theorem b2_skewIdem_not_orthogonal_aux :
    b2_skewIdem.comp b2_skewIdem = b2_skewIdem ∧
      ∃ x ∈ b2_skewIdem.range, ∃ y ∈ (AddMonoidHom.id (Fin 2 → ℤ) - b2_skewIdem).range,
        b2_stdForm x y ≠ 0 := by
  refine ⟨AddMonoidHom.ext fun x ↦ ?_, Pi.single 0 1, ⟨Pi.single 0 1, ?_⟩,
    _, ⟨Pi.single 1 1, rfl⟩, ?_⟩
  · rw [AddMonoidHom.comp_apply, b2a_skewIdem_apply, b2a_skewIdem_apply]
    ext i; fin_cases i <;> simp
  · rw [b2a_skewIdem_apply]
    ext i; fin_cases i <;> simp
  · rw [b2a_stdForm_apply, AddMonoidHom.sub_apply, b2a_skewIdem_apply]
    simp

theorem b2_two_subTorus_not_injective_aux :
    ¬ Function.Injective (b2_subTorus b2_stdF (2 • AddMonoidHom.id (Fin 2 → ℤ))) := by
  set f := 2 • AddMonoidHom.id (Fin 2 → ℤ) with hf
  have hfx : ∀ x, f x = x + x := fun x ↦ by rw [hf]; simp [two_nsmul]
  let μ : f.range := ⟨f (Pi.single 0 1), Pi.single 0 1, rfl⟩
  let w : ℂ ⊗[ℤ] f.range := ((1 / 2 : ℂ)) ⊗ₜ[ℤ] μ
  intro hinj
  have h1 : b2_subTorus b2_stdF f (QuotientAddGroup.mk (Submodule.Quotient.mk w)) = 0 := by
    change (QuotientAddGroup.mk (Submodule.Quotient.mk ((1 / 2 : ℂ) ⊗ₜ[ℤ]
      (f (Pi.single 0 1)))) : b2_torus _ b2_stdF) = 0
    rw [hfx, TensorProduct.tmul_add, ← TensorProduct.add_tmul, add_halves]
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨Pi.single 0 1, rfl⟩
  have h2 := hinj (h1.trans (map_zero _).symm)
  obtain ⟨⟨_, y, rfl⟩, hy⟩ := (b2a_torus_mk_eq_zero_iff _ w).1 h2
  change b2_cplxMap f.range.subtype _ ∈ b2_stdF at hy
  rw [map_sub] at hy
  change (1 / 2 : ℂ) ⊗ₜ[ℤ] f (Pi.single 0 1) - (1 : ℂ) ⊗ₜ[ℤ] f y ∈ b2_stdF at hy
  rw [hfx, TensorProduct.tmul_add, ← TensorProduct.add_tmul, add_halves,
    ← TensorProduct.tmul_sub] at hy
  have h3 := b2a_incl_eq_zero_of_mem b2_std_isWeightOne_aux hy
  rw [← TensorProduct.tmul_zero (R := ℤ) (Fin 2 → ℤ) (1 : ℂ)] at h3
  have h4 := congrFun (b2a_incl_injective h3) 0
  rw [hfx] at h4
  simp at h4
  omega

theorem b2_irrF_not_discrete_aux :
    ¬ DiscreteTopology (b2_latticeMap (Fin 2 → ℤ) b2_irrF).range := by
  intro hdisc
  set q₀ := b2_latticeMap _ b2_irrF (Pi.single 0 1)
  have hopen : IsOpen ({0} : Set (b2_latticeMap (Fin 2 → ℤ) b2_irrF).range) := isOpen_discrete _
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.1 hopen
  have hg : Continuous fun z : ℂ ↦ z • q₀ := by fun_prop
  have h0 : (0 : ℂ) ∈ (fun z : ℂ ↦ z • q₀) ⁻¹' U := by
    have : (0 : (b2_latticeMap (Fin 2 → ℤ) b2_irrF).range) ∈ Subtype.val ⁻¹' U := by
      rw [hUeq]; rfl
    simpa using this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hg) 0 h0
  obtain ⟨r, hr, hr0, hrε⟩ :=
    HodgeLean.Foundations.LatticeTorus.irrationalSubgroup_dense.exists_between hε
  obtain ⟨m, n, rfl⟩ := (HodgeLean.Foundations.LatticeTorus.mem_irrationalSubgroup_iff _).1 hr
  have hmem : ((m * Real.sqrt 2 + n : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0]
    exact hrε
  have hx := b2a_irr_lattice ![n, m]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx
  have hU' : (⟨b2_latticeMap _ b2_irrF ![n, m], ![n, m], rfl⟩ :
      (b2_latticeMap (Fin 2 → ℤ) b2_irrF).range) ∈ Subtype.val ⁻¹' U := by
    change b2_latticeMap _ b2_irrF ![n, m] ∈ U
    rw [hx, show (n : ℝ) + Real.sqrt 2 * m = m * Real.sqrt 2 + n by ring]
    exact hball hmem
  rw [hUeq, Set.mem_singleton_iff] at hU'
  have h1 := congrArg b2a_irrBar (congrArg Subtype.val hU')
  rw [b2a_irrBar_lattice] at h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ZeroMemClass.coe_zero, map_zero,
    Complex.ofReal_eq_zero] at h1
  linarith

theorem b2_irrF_not_t2Space_aux : ¬ T2Space (b2_torus (Fin 2 → ℤ) b2_irrF) := by
  intro hT2
  set q₀ := b2_latticeMap _ b2_irrF (Pi.single 0 1)
  set L := (b2_latticeMap (Fin 2 → ℤ) b2_irrF).range
  have hcl : IsClosed (L : Set ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_irrF)) := by
    have := (isClosed_singleton (x := (0 : b2_torus (Fin 2 → ℤ) b2_irrF))).preimage
      (QuotientAddGroup.continuous_mk (N := L))
    convert this using 1
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff, QuotientAddGroup.eq_zero_iff]
    rfl
  set S := {r : ℝ | ((r : ℂ) • q₀) ∈ L}
  have hS : IsClosed S :=
    hcl.preimage (by fun_prop : Continuous fun r : ℝ ↦ (r : ℂ) • q₀)
  have hsub : (HodgeLean.Foundations.LatticeTorus.irrationalSubgroup : Set ℝ) ⊆ S := by
    intro r hr
    obtain ⟨m, n, rfl⟩ := (HodgeLean.Foundations.LatticeTorus.mem_irrationalSubgroup_iff _).1 hr
    have hx := b2a_irr_lattice ![n, m]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx
    refine ⟨![n, m], ?_⟩
    rw [hx, show (n : ℝ) + Real.sqrt 2 * m = m * Real.sqrt 2 + n by ring]
  have hS' : S = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← HodgeLean.Foundations.LatticeTorus.irrationalSubgroup_dense.closure_eq]
    exact closure_minimal hsub hS
  have hhalf : (1 / 2 : ℝ) ∈ S := hS' ▸ Set.mem_univ _
  obtain ⟨x, hx⟩ := hhalf
  have h1 := congrArg b2a_irrBar hx
  rw [b2a_irrBar_lattice, map_smul, b2a_irrBar_lattice] at h1
  simp only [Pi.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true,
    Pi.single_eq_of_ne, Int.cast_one, Int.cast_zero, mul_zero, add_zero, Complex.ofReal_one,
    smul_eq_mul, mul_one] at h1
  have h2 : (x 0 : ℝ) + Real.sqrt 2 * x 1 = 1 / 2 := by exact_mod_cast h1
  by_cases hx1 : x 1 = 0
  · rw [hx1, Int.cast_zero, mul_zero, add_zero] at h2
    have : (2 * x 0 : ℝ) = 1 := by linarith
    have : 2 * x 0 = 1 := by exact_mod_cast this
    omega
  · apply irrational_sqrt_two
    refine ⟨(1 / 2 - x 0) / x 1, ?_⟩
    have : (x 1 : ℝ) ≠ 0 := by exact_mod_cast hx1
    push_cast
    field_simp
    linarith

end Standard

end HodgeLean.Foundations.Program
