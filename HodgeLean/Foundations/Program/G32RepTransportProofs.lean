import HodgeLean.Foundations.Program.G32RepStages

/-! # Open bodies for the G32 representation stages E and G

One auxiliary declaration per statement of `G32RepTransport.lean`: the restriction multiplicity
as an eigenspace dimension (stage E), and the transport of `U` to the primitive part of a
supplier with the complementary-line input `hco` of `g32c_gamma_invariant_of` (stage G).
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations

/-- An intertwining map out of the line `χ` is determined by its value at `1`, which is a
`χ`-eigenvector. -/
def rfd_linIntertwiningEquiv {G : Type} [Group G] [Fintype G] (σ : FDRep ℂ G)
    (H : Subgroup G) (χ : H →* ℂˣ) :
    Representation.IntertwiningMap
        ((Algebra.lmul ℂ ℂ : ℂ →* Module.End ℂ ℂ).comp ((Units.coeHom ℂ).comp χ))
        (σ.ρ.comp H.subtype) ≃ₗ[ℂ] rfd_eigen σ.ρ H χ where
  toFun f := ⟨f 1, fun h => by
    have := LinearMap.congr_fun (f.isIntertwining' h) 1
    change f (((χ h : ℂˣ) : ℂ) * 1) = σ.ρ h (f 1) at this
    rw [← this, mul_one, ← map_smul, smul_eq_mul, mul_one]⟩
  map_add' f g := rfl
  map_smul' c f := rfl
  invFun v := ⟨LinearMap.smulRight LinearMap.id v.1, fun h => by
    ext
    change (((χ h : ℂˣ) : ℂ) * 1) • v.1 = σ.ρ h ((1 : ℂ) • v.1)
    rw [mul_one, one_smul, v.2 h]⟩
  left_inv f := by
    refine Representation.IntertwiningMap.ext (LinearMap.ext_ring ?_)
    change (1 : ℂ) • f 1 = f 1
    rw [one_smul]
  right_inv v := by
    ext
    change (1 : ℂ) • v.1 = v.1
    rw [one_smul]

theorem rfd_finrank_eigen_eq_papersMult_aux {G : Type} [Group G] [Fintype G] (σ : FDRep ℂ G)
    (H : Subgroup G) (χ : H →* ℂˣ) :
    Module.finrank ℂ (rfd_eigen σ.ρ H χ) = papersMult H σ χ := by
  classical
  have : Invertible (Nat.card H : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [← (rfd_linIntertwiningEquiv σ H χ).finrank_eq, papersMult, ← Nat.cast_inj (R := ℂ),
    ← FDRep.scalar_product_char_eq_finrank_equivariant,
    ← Representation.card_inv_mul_sum_char_mul_char_eq_finrank]
  rfl

/-- The averaging projectors of `ψ` and `ψ⁻¹` are adjoint for an invariant bilinear form. -/
theorem rfd_eigenProj_adjoint {G : Type} [Group G] [Fintype G] {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G W) (ω : LinearMap.BilinForm ℂ W)
    (hω : ∀ g x y, ω (ρ g x) (ρ g y) = ω x y) (H : Subgroup G) (ψ : H →* ℂˣ) (x y : W) :
    ω (rfd_eigenProj ρ H ψ x) y = ω x (rfd_eigenProj ρ H ψ⁻¹ y) := by
  classical
  rw [rfd_eigenProj_apply, rfd_eigenProj_apply]
  simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.inv H) _ _ fun h => ?_
  simp only [Equiv.inv_apply, smul_eq_mul, MonoidHom.inv_apply, inv_inv, map_inv]
  congr 1
  have := hω (h : G) x (ρ ((h : G)⁻¹) y)
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
  rw [this, Subgroup.coe_inv]

/-- Simple representations with the same character are isomorphic. -/
theorem rfd_iso_of_character_eq {G : Type} [Group G] [Fintype G] (V W : FDRep ℂ G) [Simple V]
    [Simple W] (h : V.character = W.character) : Nonempty (V ≅ W) := by
  by_contra hne
  have h1 := FDRep.char_orthonormal V W
  have h2 := FDRep.char_orthonormal V V
  have hV : Nonempty (V ≅ V) := ⟨Iso.refl V⟩
  simp only [hne, hV, ↓reduceIte, ← h] at h1 h2
  rw [h1] at h2
  exact zero_ne_one h2

/-- **A full family of simple classes.** The characters of simple representations are
orthonormal, hence linearly independent in the finite-dimensional space `G → ℂ`; one simple
representative for each of these finitely many characters is a family of pairwise
non-isomorphic simple objects meeting every isomorphism class. -/
theorem rfd_simple_family (G : Type) [Group G] [Fintype G] :
    ∃ (Idx : Type) (_ : Fintype Idx) (σ : Idx → FDRep ℂ G), (∀ i, Simple (σ i)) ∧
      (∀ i j, Nonempty (σ i ≅ σ j) → i = j) ∧
      ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i) := by
  classical
  let S : Set (G → ℂ) := {f | ∃ τ : FDRep ℂ G, Simple τ ∧ τ.character = f}
  let σ : S → FDRep ℂ G := fun i => i.2.choose
  have hσ : ∀ i, Simple (σ i) := fun i => i.2.choose_spec.1
  have hχ : ∀ i, (σ i).character = i.1 := fun i => i.2.choose_spec.2
  have horth : ∀ i j : S, (Nat.card G : ℂ)⁻¹ * ∑ g, (i : G → ℂ) g * (j : G → ℂ) g⁻¹ =
      if i = j then 1 else 0 := by
    intro i j
    have := hσ i
    have := hσ j
    rw [← hχ i, ← hχ j, FDRep.char_orthonormal]
    congr 1
    refine propext ⟨fun ⟨e⟩ => Subtype.ext ?_, fun hij => hij ▸ ⟨Iso.refl _⟩⟩
    rw [← hχ i, ← hχ j]
    exact FDRep.char_iso e
  have hli : LinearIndependent ℂ (fun x : S => (x : G → ℂ)) := by
    rw [linearIndependent_iff']
    intro s c hc j hj
    have hpair := congrArg (fun f : G → ℂ => (Nat.card G : ℂ)⁻¹ * ∑ g, f g * (j : G → ℂ) g⁻¹) hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, mul_zero, Finset.sum_mul] at hpair
    rw [Finset.sum_comm, Finset.mul_sum] at hpair
    have hterm : ∀ i ∈ s, (Nat.card G : ℂ)⁻¹ * ∑ g, c i * (i : G → ℂ) g * (j : G → ℂ) g⁻¹ =
        if i = j then c i else 0 := by
      intro i _
      simp_rw [mul_assoc, ← Finset.mul_sum, mul_left_comm, horth, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s j] at hpair
    simpa [hj] using hpair
  have hfin : S.Finite := hli.setFinite
  refine ⟨S, hfin.fintype, σ, hσ, fun i j ⟨e⟩ => Subtype.ext ?_, fun τ hτ => ?_⟩
  · rw [← hχ i, ← hχ j]
    exact FDRep.char_iso e
  · refine ⟨⟨τ.character, τ, hτ, rfl⟩, ?_⟩
    have := hσ ⟨τ.character, τ, hτ, rfl⟩
    exact rfd_iso_of_character_eq _ _ (hχ ⟨τ.character, τ, hτ, rfl⟩).symm

/-- Isomorphic representations have the same restriction multiplicities. -/
theorem rfd_papersMult_iso {G : Type} [Group G] [Fintype G] (H : Subgroup G) {V W : FDRep ℂ G}
    (e : V ≅ W) (ψ : H →* ℂˣ) : papersMult H V ψ = papersMult H W ψ := by
  classical
  have : Invertible (Nat.card H : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [← Nat.cast_inj (R := ℂ), papersMult, papersMult,
    ← FDRep.scalar_product_char_eq_finrank_equivariant,
    ← FDRep.scalar_product_char_eq_finrank_equivariant]
  have hc : ∀ h : H, (papersResRep H V).character h = (papersResRep H W).character h :=
    fun h => congrFun (FDRep.char_iso e) (h : G)
  simp only [hc]

/-- On the top exterior power, an endomorphism acts by its determinant. -/
theorem rfd_exteriorPower_map_top {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] {n : ℕ} (hn : Module.finrank ℂ M = n) (f : Module.End ℂ M)
    (z : ⋀[ℂ]^n M) : exteriorPower.map n f z = LinearMap.det f • z := by
  let b : Module.Basis (Fin n) ℂ M := Module.finBasisOfFinrankEq ℂ M hn
  suffices h : exteriorPower.map n f = LinearMap.det f • LinearMap.id by
    rw [h, LinearMap.smul_apply, LinearMap.id_apply]
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
  simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti,
    LinearMap.smul_apply, LinearMap.id_apply]
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hg := (φ.compAlternatingMap (exteriorPower.ιMulti ℂ n)).eq_smul_basis_det b
  have h1 := congrArg (fun g : M [⋀^Fin n]→ₗ[ℂ] ℂ => g (f ∘ v)) hg
  have h2 := congrArg (fun g : M [⋀^Fin n]→ₗ[ℂ] ℂ => g v) hg
  simp only [LinearMap.compAlternatingMap_apply, smul_apply, smul_eq_mul] at h1 h2
  rw [map_sub, map_smul, h1, h2, Module.Basis.det_comp, smul_eq_mul]
  ring

/-- The determinant of an endomorphism preserving two complementary subspaces is the product of
the determinants of its restrictions. -/
theorem rfd_det_eq_mul_of_isCompl {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (f : Module.End ℂ M) {p q : Submodule ℂ M} (h : IsCompl p q)
    (hp : ∀ x ∈ p, f x ∈ p) (hq : ∀ x ∈ q, f x ∈ q) :
    LinearMap.det f = LinearMap.det (f.restrict hp) * LinearMap.det (f.restrict hq) := by
  let e := Submodule.prodEquivOfIsCompl p q h
  have hconj' : f ∘ₗ (e : (p × q) →ₗ[ℂ] M) =
      (e : (p × q) →ₗ[ℂ] M) ∘ₗ LinearMap.prodMap (f.restrict hp) (f.restrict hq) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, b⟩ := x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.prodMap_apply, e,
      Submodule.coe_prodEquivOfIsCompl', map_add, LinearMap.coe_restrict_apply]
  have hconj : f = (e : (p × q) →ₗ[ℂ] M) ∘ₗ (LinearMap.prodMap (f.restrict hp) (f.restrict hq))
      ∘ₗ (e.symm : M →ₗ[ℂ] (p × q)) := by
    refine LinearMap.ext fun x => ?_
    have := LinearMap.congr_fun hconj' (e.symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, this]
  calc LinearMap.det f = LinearMap.det ((e : (p × q) →ₗ[ℂ] M) ∘ₗ
        (LinearMap.prodMap (f.restrict hp) (f.restrict hq)) ∘ₗ (e.symm : M →ₗ[ℂ] (p × q))) :=
        congrArg _ hconj
    _ = _ := by rw [LinearMap.det_conj, LinearMap.det_prodMap]

end HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

variable {A : g32t_Sixfold}

/-! ### Base change of kernels -/

/-- Base change along `ℚ → ℂ` commutes with kernels (`ℂ` is flat over `ℚ`). -/
theorem g32rep_baseChange_ker {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] (f : V →ₗ[ℚ] W) :
    (LinearMap.ker f).baseChange ℂ = LinearMap.ker (f.baseChange ℂ) :=
  (Module.Flat.ker_lTensor_eq (R := ℚ) ℂ ℂ f).symm

/-- Base change along `ℚ → ℂ` commutes with ranges. -/
theorem g32rep_range_baseChange {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] (f : V →ₗ[ℚ] W) :
    LinearMap.range (f.baseChange ℂ) = (LinearMap.range f).baseChange ℂ := by
  conv_lhs => rw [← LinearMap.subtype_comp_rangeRestrict f]
  rw [LinearMap.baseChange_comp, LinearMap.range_comp_of_range_eq_top]
  · rfl
  · exact LinearMap.range_eq_top.2 (LinearMap.baseChange_surjective ℂ f.surjective_rangeRestrict)

/-- Base change along `ℚ → ℂ` commutes with finite intersections of kernels. -/
theorem g32rep_baseChange_iInf_ker {Idx V W : Type*} [Finite Idx] [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (f : Idx → V →ₗ[ℚ] W) :
    (⨅ i, LinearMap.ker (f i)).baseChange ℂ = ⨅ i, LinearMap.ker ((f i).baseChange ℂ) := by
  classical
  have := Fintype.ofFinite Idx
  rw [← LinearMap.ker_pi, g32rep_baseChange_ker]
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_iInf]
  have key : ∀ i, TensorProduct.piRight ℚ ℂ ℂ (fun _ : Idx => W)
      ((LinearMap.pi f).baseChange ℂ x) i = (f i).baseChange ℂ x := by
    intro i
    induction x using TensorProduct.inductionOn with
    | tmul a v => simp
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  constructor
  · intro h i
    rw [← key, h, map_zero]
    rfl
  · intro h
    apply (TensorProduct.piRight ℚ ℂ ℂ (fun _ : Idx => W)).injective
    funext i
    rw [key, h i, map_zero]
    rfl

/-! ### Polynomials in commuting operators -/

theorem g32rep_commute_aeval {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B] {a b : B}
    (h : Commute a b) (p : Polynomial R) : Commute a (Polynomial.aeval b p) := by
  induction p using Polynomial.induction_on with
  | C r => rw [Polynomial.aeval_C]; exact (Algebra.commutes r a).symm
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n r hn =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    exact hn.mul_right h

theorem g32rep_aeval_intertwine {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {a : Module.End R M} {b : Module.End R N}
    (h : f ∘ₗ a = b ∘ₗ f) (p : Polynomial R) :
    f ∘ₗ Polynomial.aeval a p = Polynomial.aeval b p ∘ₗ f := by
  induction p using Polynomial.induction_on with
  | C r =>
    rw [Polynomial.aeval_C, Polynomial.aeval_C, Module.algebraMap_end_eq_smul_id,
      Module.algebraMap_end_eq_smul_id, LinearMap.comp_smul, LinearMap.smul_comp,
      LinearMap.comp_id, LinearMap.id_comp]
  | add p q hp hq => rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hp, hq]
  | monomial n r hn =>
    have ea : Polynomial.aeval a (Polynomial.C r * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval a (Polynomial.C r * Polynomial.X ^ n) ∘ₗ a := by
      rw [map_mul, Polynomial.aeval_X]; rfl
    have eb : Polynomial.aeval b (Polynomial.C r * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval b (Polynomial.C r * Polynomial.X ^ n) ∘ₗ b := by
      rw [map_mul, Polynomial.aeval_X]; rfl
    rw [pow_succ, ← mul_assoc, ea, eb, ← LinearMap.comp_assoc, hn, LinearMap.comp_assoc, h,
      LinearMap.comp_assoc]

theorem g32rep_baseChange_aeval {V : Type*} [AddCommGroup V] [Module ℚ V]
    (a : Module.End ℚ V) (p : Polynomial ℚ) :
    (Polynomial.aeval a p).baseChange ℂ = Polynomial.aeval (a.baseChange ℂ) p :=
  (Polynomial.aeval_algHom_apply (Module.End.baseChangeHom ℚ ℂ V) a p).symm

/-! ### The primitive part as a finite intersection of kernels -/

/-- The operators whose kernels cut out the primitive part: `(aut h)^* - 1` for `χ h = 1` and
`Φ_m((aut h)^*)` for `χ h = ofAdd 1` (and `0` otherwise). -/
def g32rep_primOp {J : Over (Spec ↧ℂ)} [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) : S.H ⊕ S.H → Module.End ℚ (HQ J 1)
  | Sum.inl h => by
    classical
    exact if S.χ h = 1 then homPullback (aut h) 1 - LinearMap.id else 0
  | Sum.inr h => by
    classical
    exact if S.χ h = Multiplicative.ofAdd 1 then
      Polynomial.aeval (homPullback (aut h) 1) (Polynomial.cyclotomic S.m ℚ) else 0

theorem g32rep_primitive_eq_iInf {J : Over (Spec ↧ℂ)} [IsIntegral J.left] [Smooth J.hom]
    [IsProjective J.hom] (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) :
    g32p_primitive aut S = ⨅ i, LinearMap.ker (g32rep_primOp aut S i) := by
  classical
  ext x
  simp only [g32p_primitive, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_eqLocus,
    LinearMap.mem_ker, Sum.forall, g32rep_primOp, LinearMap.id_apply]
  refine and_congr (forall_congr' fun h => ?_) (forall_congr' fun h => ?_)
  · by_cases hh : S.χ h = 1
    · simp only [hh, ite_true, forall_const, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    · simp [hh]
  · by_cases hh : S.χ h = Multiplicative.ofAdd 1
    · simp only [hh, ite_true, forall_const]
    · simp [hh]

theorem g32rep_primitive_baseChange {J : Over (Spec ↧ℂ)} [IsIntegral J.left] [Smooth J.hom]
    [IsProjective J.hom] (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) :
    (g32p_primitive aut S).baseChange ℂ =
      ⨅ i, LinearMap.ker ((g32rep_primOp aut S i).baseChange ℂ) := by
  rw [g32rep_primitive_eq_iInf, g32rep_baseChange_iInf_ker]

/-- Every `u ∈ U` commutes with the complexified primitive-part operators. -/
theorem g32rep_comm_primOp (X : g32p_Cover A) (S : g32p_Supplier)
    {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X) (i : S.H ⊕ S.H) :
    u ∘ₗ (g32rep_primOp X.aut S i).baseChange ℂ = (g32rep_primOp X.aut S i).baseChange ℂ ∘ₗ u := by
  classical
  rcases i with h | h
  · simp only [g32rep_primOp]
    split_ifs
    · rw [LinearMap.baseChange_sub, LinearMap.baseChange_id, LinearMap.comp_sub,
        LinearMap.sub_comp, hu.2.1 h, LinearMap.comp_id, LinearMap.id_comp]
    · rw [LinearMap.baseChange_zero, LinearMap.comp_zero, LinearMap.zero_comp]
  · simp only [g32rep_primOp]
    split_ifs
    · rw [g32rep_baseChange_aeval]
      exact g32rep_commute_aeval (R := ℚ) (hu.2.1 h) _
    · rw [LinearMap.baseChange_zero, LinearMap.comp_zero, LinearMap.zero_comp]

theorem g32rep_primitive_preserved_aux (X : g32p_Cover A) (S : g32p_Supplier)
    {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X) :
    ∀ x ∈ (g32p_primitive X.aut S).baseChange ℂ,
      u x ∈ (g32p_primitive X.aut S).baseChange ℂ := by
  intro x hx
  rw [g32rep_primitive_baseChange] at hx ⊢
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro i
  rw [← LinearMap.comp_apply, ← g32rep_comm_primOp X S hu i, LinearMap.comp_apply, hx i,
    map_zero]

/-! ### The retraction -/

theorem g32rep_incl_proj (X : g32p_Cover A) (S : g32p_Supplier) (hS : g32p_Admissible X.aut S) :
    homPullback (X.part S hS).incl 1 ∘ₗ homPullback (X.part S hS).proj 1 =
      ((X.part S hS).N : ℚ) • LinearMap.id := by
  rw [← spec_homPullback_comp, (X.part S hS).retract, ← zpow_natCast, spec_homPullback_zpow,
    spec_homPullback_id, Int.cast_natCast]

theorem g32rep_incl_proj_C (X : g32p_Cover A) (S : g32p_Supplier) (hS : g32p_Admissible X.aut S)
    (y : ℂ ⊗[ℚ] HQ (X.part S hS).P 1) :
    (homPullback (X.part S hS).incl 1).baseChange ℂ
        ((homPullback (X.part S hS).proj 1).baseChange ℂ y) = ((X.part S hS).N : ℂ) • y := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, g32rep_incl_proj,
    LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply]
  exact (algebraMap_smul ℂ ((X.part S hS).N : ℚ) y).symm.trans (by simp)

theorem g32rep_proj_injective (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) :
    Function.Injective ((homPullback (X.part S hS).proj 1).baseChange ℂ) := by
  intro y z hyz
  have hN : ((X.part S hS).N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (X.part S hS).N_pos.ne'
  have := congrArg ((homPullback (X.part S hS).incl 1).baseChange ℂ) hyz
  rw [g32rep_incl_proj_C, g32rep_incl_proj_C] at this
  exact smul_right_injective _ hN this

theorem g32rep_range_proj (X : g32p_Cover A) (S : g32p_Supplier) (hS : g32p_Admissible X.aut S) :
    LinearMap.range ((homPullback (X.part S hS).proj 1).baseChange ℂ) =
      (g32p_primitive X.aut S).baseChange ℂ := by
  rw [g32rep_range_baseChange, (X.part S hS).image]

theorem g32rep_restrict_proj_aux (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X) :
    (homPullback (X.part S hS).proj 1).baseChange ℂ ∘ₗ
        g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u =
      u ∘ₗ (homPullback (X.part S hS).proj 1).baseChange ℂ := by
  refine LinearMap.ext fun y => ?_
  have hmem : u ((homPullback (X.part S hS).proj 1).baseChange ℂ y) ∈
      LinearMap.range ((homPullback (X.part S hS).proj 1).baseChange ℂ) := by
    rw [g32rep_range_proj]
    exact g32rep_primitive_preserved_aux X S hu _
      (by rw [← g32rep_range_proj X S hS]; exact LinearMap.mem_range_self _ y)
  obtain ⟨z, hz⟩ := hmem
  have hN : ((X.part S hS).N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (X.part S hS).N_pos.ne'
  have hR : g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u y = z := by
    simp only [g32c_restrict, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [← hz, g32rep_incl_proj_C, smul_smul, inv_mul_cancel₀ hN, one_smul]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hR, hz]

/-! ### The cyclotomic action through `H′` -/

instance g32rep_fact_one_lt (S : g32p_Supplier) : Fact (1 < S.m) :=
  ⟨by have := S.three_le; omega⟩

/-- Every element of `ℚ(μ_m)` is a polynomial in `ζ`. -/
theorem g32rep_exists_aeval_zeta (S : g32p_Supplier) (a : cyc_Field S.m) :
    ∃ p : Polynomial ℚ, Polynomial.aeval (g32p_zeta S) p = a := by
  have h := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := ℚ)
    (IsCyclotomicExtension.zeta_spec S.m ℚ (cyc_Field S.m))
  have ha : a ∈ Algebra.adjoin ℚ {g32p_zeta S} := by
    rw [g32p_zeta, h]
    exact Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨p, hp⟩ := ha
  exact ⟨p, hp⟩

/-- A generator of `H′` modulo `ker χ`. -/
theorem g32rep_exists_gen (S : g32p_Supplier) :
    ∃ h₀ : S.H, S.χ h₀ = Multiplicative.ofAdd 1 ∧ g32p_fieldValue S h₀ = g32p_zeta S := by
  obtain ⟨h₀, hh₀⟩ := S.surjective (Multiplicative.ofAdd 1)
  refine ⟨h₀, hh₀, ?_⟩
  rw [g32p_fieldValue, hh₀, toAdd_ofAdd, ZMod.val_one, pow_one]

/-- `proj^*` carries the action of a polynomial in `ζ` to the same polynomial in `(aut h₀)^*`. -/
theorem g32rep_proj_aeval (X : g32p_Cover A) (S : g32p_Supplier) (hS : g32p_Admissible X.aut S)
    {h₀ : S.H} (hh₀ : g32p_fieldValue S h₀ = g32p_zeta S) (p : Polynomial ℚ) :
    homPullback (X.part S hS).proj 1 ∘ₗ
        cyc_scalar (X.part S hS).act.cyc_coordinates (Polynomial.aeval (g32p_zeta S) p) =
      Polynomial.aeval (homPullback (X.aut h₀) 1) p ∘ₗ homPullback (X.part S hS).proj 1 := by
  have h1 := (X.part S hS).equivariant h₀
  rw [hh₀] at h1
  have h2 := g32rep_aeval_intertwine _ h1 p
  have h3 : cyc_scalar (X.part S hS).act.cyc_coordinates (Polynomial.aeval (g32p_zeta S) p) =
      Polynomial.aeval (cyc_scalar (X.part S hS).act.cyc_coordinates (g32p_zeta S)) p :=
    (Polynomial.aeval_algHom_apply (cyc_rep (X.part S hS).act.cyc_coordinates) (g32p_zeta S) p).symm
  rw [h3, h2]

theorem g32rep_proj_aeval_C (X : g32p_Cover A) (S : g32p_Supplier) (hS : g32p_Admissible X.aut S)
    {h₀ : S.H} (hh₀ : g32p_fieldValue S h₀ = g32p_zeta S) (p : Polynomial ℚ) :
    (homPullback (X.part S hS).proj 1).baseChange ℂ ∘ₗ
        (cyc_scalar (X.part S hS).act.cyc_coordinates (Polynomial.aeval (g32p_zeta S) p)).baseChange ℂ =
      Polynomial.aeval (g32rep_rep X h₀) p ∘ₗ (homPullback (X.part S hS).proj 1).baseChange ℂ := by
  rw [← LinearMap.baseChange_comp, g32rep_proj_aeval X S hS hh₀ p, LinearMap.baseChange_comp,
    g32rep_baseChange_aeval]
  rfl

theorem g32rep_restrict_cyc_aux (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X)
    (a : cyc_Field S.m) :
    g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u ∘ₗ
        (cyc_scalar (X.part S hS).act.cyc_coordinates a).baseChange ℂ =
      (cyc_scalar (X.part S hS).act.cyc_coordinates a).baseChange ℂ ∘ₗ
        g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u := by
  obtain ⟨p, rfl⟩ := g32rep_exists_aeval_zeta S a
  obtain ⟨h₀, -, hh₀⟩ := g32rep_exists_gen S
  apply (LinearMap.cancel_left (g32rep_proj_injective X S hS)).1
  refine LinearMap.ext fun y => ?_
  have e1 := LinearMap.congr_fun (g32rep_restrict_proj_aux X S hS hu)
  have e2 := LinearMap.congr_fun (g32rep_proj_aeval_C X S hS hh₀ p)
  have e3 : ∀ x, u (Polynomial.aeval (g32rep_rep X h₀) p x) =
      Polynomial.aeval (g32rep_rep X h₀) p (u x) := fun x =>
    LinearMap.congr_fun (g32rep_commute_aeval (R := ℚ) (b := g32rep_rep X h₀) (hu.2.1 h₀) p).eq x
  simp only [LinearMap.comp_apply] at e1 e2 ⊢
  rw [e1, e2, e3, ← e1 y, ← e2]

/-- The values of `χc ^ k` are the values of `t` on the field values. -/
theorem g32rep_charPow_apply (S : g32p_Supplier) (χc : S.H →* ℂˣ)
    (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)
    (k : ℤ) (t : cyc_Field S.m →ₐ[ℚ] ℂ) (ht : t (g32p_zeta S) = g32p_root S.m ^ k) (h : S.H) :
    (((χc ^ k) h : ℂˣ) : ℂ) = t (g32p_fieldValue S h) := by
  rw [MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val, hχc, g32p_fieldValue, map_pow, ht,
    ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

/-- `proj^*` carries the action of `cyc_scalar (fieldValue h)` to `(aut h)^*`, complexified. -/
theorem g32rep_proj_fieldValue_C (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) (h : S.H) (y : ℂ ⊗[ℚ] HQ (X.part S hS).P 1) :
    (homPullback (X.part S hS).proj 1).baseChange ℂ
        ((cyc_scalar (X.part S hS).act.cyc_coordinates (g32p_fieldValue S h)).baseChange ℂ y) =
      g32rep_rep X h ((homPullback (X.part S hS).proj 1).baseChange ℂ y) := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, (X.part S hS).equivariant h,
    LinearMap.baseChange_comp]
  rfl

theorem g32rep_proj_eigen_aux (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) (χc : S.H →* ℂˣ)
    (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)
    (k : ℤ) (t : cyc_Field S.m →ₐ[ℚ] ℂ) (ht : t (g32p_zeta S) = g32p_root S.m ^ k) :
    (cyc_eigenspace (X.part S hS).act.cyc_coordinates t).map
        ((homPullback (X.part S hS).proj 1).baseChange ℂ) =
      rfd_eigen (g32rep_rep X) S.H (χc ^ k) := by
  have hval := g32rep_charPow_apply S χc hχc k t ht
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩ h
    simp only [SetLike.mem_coe, cyc_eigenspace, Submodule.mem_iInf,
      Module.End.mem_eigenspace_iff] at hy
    change g32rep_rep X h _ = _
    rw [← g32rep_proj_fieldValue_C, hy, map_smul, hval]
  · intro w hw
    obtain ⟨h₀, hh₀χ, hh₀⟩ := g32rep_exists_gen S
    have hw₀ : g32rep_rep X h₀ w = t (g32p_zeta S) • w := by
      rw [hw h₀, hval, hh₀]
    -- `w` lies in the complexified primitive part
    have hprim : w ∈ (g32p_primitive X.aut S).baseChange ℂ := by
      classical
      rw [g32rep_primitive_baseChange]
      simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      rintro (h | h) <;> simp only [g32rep_primOp]
      · split_ifs with hh
        · rw [LinearMap.baseChange_sub, LinearMap.baseChange_id, LinearMap.sub_apply,
            LinearMap.id_apply, sub_eq_zero]
          change g32rep_rep X h w = w
          rw [hw h, hval, g32p_fieldValue, hh, toAdd_one, ZMod.val_zero, pow_zero, map_one,
            one_smul]
        · rw [LinearMap.baseChange_zero, LinearMap.zero_apply]
      · split_ifs with hh
        · have hwh : g32rep_rep X h w = t (g32p_zeta S) • w := by
            rw [hw h, hval, g32p_fieldValue, hh, toAdd_ofAdd, ZMod.val_one, pow_one]
          rw [g32rep_baseChange_aeval, ← Polynomial.aeval_map_algebraMap ℂ]
          change Polynomial.aeval (g32rep_rep X h) _ w = 0
          rw [Module.End.aeval_apply_of_mem_apply_eq_smul hwh, Polynomial.eval_map_algebraMap,
            Polynomial.aeval_algHom_apply, g32p_zeta, IsCyclotomicExtension.aeval_zeta, map_zero,
            zero_smul]
        · rw [LinearMap.baseChange_zero, LinearMap.zero_apply]
    rw [← g32rep_range_proj X S hS] at hprim
    obtain ⟨y, rfl⟩ := hprim
    refine ⟨y, ?_, rfl⟩
    simp only [SetLike.mem_coe, cyc_eigenspace, Submodule.mem_iInf,
      Module.End.mem_eigenspace_iff]
    intro a
    obtain ⟨p, rfl⟩ := g32rep_exists_aeval_zeta S a
    apply g32rep_proj_injective X S hS
    have e2 := LinearMap.congr_fun (g32rep_proj_aeval_C X S hS hh₀ p) y
    rw [LinearMap.comp_apply] at e2
    rw [e2, LinearMap.comp_apply, ← Polynomial.aeval_map_algebraMap ℂ,
      Module.End.aeval_apply_of_mem_apply_eq_smul hw₀, Polynomial.eval_map_algebraMap,
      Polynomial.aeval_algHom_apply, map_smul]

/-! ### Nondegeneracy of the polarization form on the primitive part -/

theorem g32rep_root_prim (m : ℕ) (hm : m ≠ 0) : IsPrimitiveRoot (g32p_root m) m :=
  Complex.isPrimitiveRoot_exp m hm

theorem g32rep_root_ne_zero (m : ℕ) : g32p_root m ≠ 0 := Complex.exp_ne_zero _

/-- The complex character `h ↦ exp(2πi/m)^{χ(h)}` of `H′`. -/
def g32rep_chi (S : g32p_Supplier) : S.H →* ℂˣ where
  toFun h := Units.mk0 (g32p_root S.m) (g32rep_root_ne_zero S.m) ^ (Multiplicative.toAdd (S.χ h)).val
  map_one' := by simp
  map_mul' a b := by
    have hm : (Units.mk0 (g32p_root S.m) (g32rep_root_ne_zero S.m)) ^ S.m = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      exact (g32rep_root_prim S.m (NeZero.ne S.m)).pow_eq_one
    rw [map_mul, toAdd_mul, ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div ((Multiplicative.toAdd (S.χ a)).val +
      (Multiplicative.toAdd (S.χ b)).val) S.m, pow_add, pow_mul, hm, one_pow, mul_one]

theorem g32rep_chi_apply (S : g32p_Supplier) (h : S.H) :
    ((g32rep_chi S h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val := by
  change ((Units.mk0 _ _ ^ _ : ℂˣ) : ℂ) = _
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]

/-- Membership in the complexified primitive part. -/
theorem g32rep_mem_primC (X : g32p_Cover A) (S : g32p_Supplier) (v : ℂ ⊗[ℚ] HQ X.J 1) :
    v ∈ (g32p_primitive X.aut S).baseChange ℂ ↔
      (∀ h : S.H, S.χ h = 1 → g32rep_rep X h v = v) ∧
      ∀ h : S.H, S.χ h = Multiplicative.ofAdd 1 →
        Polynomial.aeval (g32rep_rep X h) (Polynomial.cyclotomic S.m ℂ) v = 0 := by
  classical
  rw [g32rep_primitive_baseChange]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, Sum.forall, g32rep_primOp]
  refine and_congr (forall_congr' fun h => ?_) (forall_congr' fun h => ?_)
  · split_ifs with hh
    · rw [LinearMap.baseChange_sub, LinearMap.baseChange_id, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      exact ⟨fun H _ => H, fun H => H hh⟩
    · simp [hh]
  · split_ifs with hh
    · rw [g32rep_baseChange_aeval, ← Polynomial.aeval_map_algebraMap ℂ,
        Polynomial.map_cyclotomic]
      exact ⟨fun H _ => H, fun H => H hh⟩
    · simp [hh]

section Char

variable (X : g32p_Cover A) (S : g32p_Supplier) (χc : S.H →* ℂˣ)
  (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)

include hχc in
theorem g32rep_chi_one {h : S.H} (hh : S.χ h = 1) : ((χc h : ℂˣ) : ℂ) = 1 := by
  rw [hχc, hh, toAdd_one, ZMod.val_zero, pow_zero]

include hχc in
theorem g32rep_chi_gen {h : S.H} (hh : S.χ h = Multiplicative.ofAdd 1) :
    ((χc h : ℂˣ) : ℂ) = g32p_root S.m := by
  rw [hχc, hh, toAdd_ofAdd, ZMod.val_one, pow_one]

include hχc in
/-- An eigenvector of `χc ^ j` with `j` prime to `m` is primitive. -/
theorem g32rep_eigen_le_primC (j : ℤ) (hj : IsPrimitiveRoot (g32p_root S.m ^ j) S.m) :
    rfd_eigen (g32rep_rep X) S.H (χc ^ j) ≤ (g32p_primitive X.aut S).baseChange ℂ := by
  intro w hw
  rw [g32rep_mem_primC]
  refine ⟨fun h hh => ?_, fun h hh => ?_⟩
  · rw [hw h, MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val, g32rep_chi_one S χc hχc hh,
      one_zpow, one_smul]
  · have hwh : g32rep_rep X h w = (g32p_root S.m ^ j) • w := by
      rw [hw h, MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val, g32rep_chi_gen S χc hχc hh]
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul hwh, (hj.isRoot_cyclotomic (NeZero.pos S.m)).eq_zero, zero_smul]

include hχc in
/-- The projectors of the characters `χc ^ n`, `n < m`, sum to a nonzero multiple of the identity on
`ker χ`-fixed vectors. -/
theorem g32rep_sum_eigenProj (v : ℂ ⊗[ℚ] HQ X.J 1)
    (hK : ∀ h : S.H, S.χ h = 1 → g32rep_rep X h v = v) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∑ n ∈ Finset.range S.m, rfd_eigenProj (g32rep_rep X) S.H (χc ^ n) v = c • v := by
  classical
  have hprim := g32rep_root_prim S.m (NeZero.ne S.m)
  have hterm : ∀ h : S.H, (∑ n ∈ Finset.range S.m, ((((χc ^ n) h)⁻¹ : ℂˣ) : ℂ)) •
      g32rep_rep X h v = if S.χ h = 1 then (S.m : ℂ) • v else 0 := by
    intro h
    have hval : ∀ n, ((((χc ^ n) h)⁻¹ : ℂˣ) : ℂ) = (((χc h : ℂˣ) : ℂ))⁻¹ ^ n := fun n => by
      rw [Units.val_inv_eq_inv_val, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, inv_pow]
    simp only [hval]
    by_cases hh : S.χ h = 1
    · simp only [hh, ↓reduceIte]
      rw [g32rep_chi_one S χc hχc hh, inv_one]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, hK h hh]
    · simp only [hh, ↓reduceIte]
      have hne : (Multiplicative.toAdd (S.χ h)).val ≠ 0 := by
        rw [Ne, ZMod.val_eq_zero]
        exact fun h0 => hh (by rw [← ofAdd_toAdd (S.χ h), h0, ofAdd_zero])
      have hw1 : (((χc h : ℂˣ) : ℂ))⁻¹ ≠ 1 := by
        rw [Ne, inv_eq_one, hχc]
        exact hprim.pow_ne_one_of_pos_of_lt hne (ZMod.val_lt _)
      have hwm : ((((χc h : ℂˣ) : ℂ))⁻¹) ^ S.m = 1 := by
        rw [inv_pow, hχc, ← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow, inv_one]
      rw [geom_sum_eq hw1, hwm, sub_self, zero_div, zero_smul]
  refine ⟨(Fintype.card S.H : ℂ)⁻¹ *
    ((Finset.univ.filter fun h : S.H => S.χ h = 1).card * S.m), ?_, ?_⟩
  · refine mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero))
      (mul_ne_zero (Nat.cast_ne_zero.2 ?_) (Nat.cast_ne_zero.2 (NeZero.ne S.m)))
    exact Finset.card_ne_zero.2 ⟨1, by simp⟩
  · simp only [rfd_eigenProj_apply]
    rw [← Finset.smul_sum, Finset.sum_comm]
    simp only [← Finset.sum_smul, hterm]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, mul_smul, mul_smul,
      ← Nat.cast_smul_eq_nsmul ℂ]

include hχc in
/-- For `n` not prime to `m`, the `χc ^ n`-projection of a primitive vector vanishes. -/
theorem g32rep_eigenProj_nonunit {v : ℂ ⊗[ℚ] HQ X.J 1}
    (hv : v ∈ (g32p_primitive X.aut S).baseChange ℂ) (n : ℕ) (hn : ¬ n.Coprime S.m) :
    rfd_eigenProj (g32rep_rep X) S.H (χc ^ n) v = 0 := by
  classical
  obtain ⟨h₀, hh₀, -⟩ := g32rep_exists_gen S
  rw [g32rep_mem_primC] at hv
  set z := rfd_eigenProj (g32rep_rep X) S.H (χc ^ n) v
  have hz : g32rep_rep X h₀ z = g32p_root S.m ^ n • z := by
    rw [rfd_eigenProj_mem (g32rep_rep X) S.H (χc ^ n) v h₀, MonoidHom.pow_apply,
      Units.val_pow_eq_pow_val, g32rep_chi_gen S χc hχc hh₀]
  have hterm : ∀ h : S.H,
      Polynomial.aeval (g32rep_rep X h₀) (Polynomial.cyclotomic S.m ℂ) (g32rep_rep X h v) = 0 := by
    intro h
    have hint : g32rep_rep X h ∘ₗ g32rep_rep X ((h⁻¹ * h₀ * h : S.H) : g32p_G) =
        g32rep_rep X h₀ ∘ₗ g32rep_rep X h := by
      change g32rep_rep X h * g32rep_rep X _ = g32rep_rep X h₀ * g32rep_rep X h
      rw [← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
      congr 2
      group
    have hk : S.χ (h⁻¹ * h₀ * h) = Multiplicative.ofAdd 1 := by
      rw [map_mul, map_mul, map_inv, mul_comm (S.χ h)⁻¹, inv_mul_cancel_right, hh₀]
    rw [← LinearMap.comp_apply, ← g32rep_aeval_intertwine _ hint, LinearMap.comp_apply,
      hv.2 _ hk, map_zero]
  have hΦ : Polynomial.aeval (g32rep_rep X h₀) (Polynomial.cyclotomic S.m ℂ) z = 0 := by
    simp only [z, rfd_eigenProj_apply, map_smul, map_sum, hterm, smul_zero,
      Finset.sum_const_zero]
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul hz] at hΦ
  refine (smul_eq_zero.1 hΦ).resolve_left fun h0 => hn ?_
  have hroot : (Polynomial.cyclotomic S.m ℂ).IsRoot (g32p_root S.m ^ n) := h0
  rw [Polynomial.isRoot_cyclotomic_iff] at hroot
  exact ((g32rep_root_prim S.m (NeZero.ne S.m)).pow_iff_coprime (NeZero.pos S.m) n).1 hroot

end Char

/-- The polarization form is nondegenerate on the complexified primitive part. -/
theorem g32rep_primC_nondeg (X : g32p_Cover A) (S : g32p_Supplier) {v : ℂ ⊗[ℚ] HQ X.J 1}
    (hv : v ∈ (g32p_primitive X.aut S).baseChange ℂ)
    (horth : ∀ w ∈ (g32p_primitive X.aut S).baseChange ℂ, g32rep_form X v w = 0) : v = 0 := by
  classical
  have hχc := g32rep_chi_apply S
  have hprim := g32rep_root_prim S.m (NeZero.ne S.m)
  obtain ⟨c, hc, hsum⟩ := g32rep_sum_eigenProj X S (g32rep_chi S) hχc v
    ((g32rep_mem_primC X S v).1 hv).1
  refine (g32rep_form_spec X).1.1 v fun y => ?_
  have hω := (g32rep_form_spec X).2.2.1
  have key : c * g32rep_form X v y = 0 := by
    rw [← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul, ← hsum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun n _ => ?_
    by_cases hn : n.Coprime S.m
    · rw [rfd_eigenProj_adjoint _ _ hω]
      apply horth
      have hinv : (g32rep_chi S ^ n)⁻¹ = g32rep_chi S ^ (-(n : ℤ)) := by
        rw [zpow_neg, zpow_natCast]
      rw [hinv]
      refine g32rep_eigen_le_primC X S (g32rep_chi S) hχc (-(n : ℤ)) ?_ ?_
      · rw [zpow_neg, zpow_natCast]
        exact (hprim.pow_of_coprime n hn).inv
      · rw [← hinv]
        exact rfd_eigenProj_mem _ _ _ y
    · rw [g32rep_eigenProj_nonunit X S (g32rep_chi S) hχc hv n hn, map_zero,
        LinearMap.zero_apply]
  exact (mul_eq_zero.1 key).resolve_left hc

theorem g32rep_det_restrict_aux (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X) :
    LinearMap.det (g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u) = 1 := by
  let := (torusCohomology_cupProductOf (X.part S hS).P).finite
  set Pc := (homPullback (X.part S hS).proj 1).baseChange ℂ with hPc
  have hrange := g32rep_range_proj X S hS
  have hpres : ∀ x ∈ LinearMap.range Pc, u x ∈ LinearMap.range Pc := by
    intro x hx
    rw [hrange] at hx ⊢
    exact g32rep_primitive_preserved_aux X S hu x hx
  let e : (ℂ ⊗[ℚ] HQ (X.part S hS).P 1) ≃ₗ[ℂ] LinearMap.range Pc :=
    LinearEquiv.ofInjective Pc (g32rep_proj_injective X S hS)
  have hconj : g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u =
      (e.symm : _ →ₗ[ℂ] _) ∘ₗ u.restrict hpres ∘ₗ (e.symm.symm : _ →ₗ[ℂ] _) := by
    refine LinearMap.ext fun y => e.injective ?_
    rw [LinearEquiv.symm_symm]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [LinearMap.restrict_apply]
    change Pc _ = u (Pc y)
    exact LinearMap.congr_fun (g32rep_restrict_proj_aux X S hS hu) y
  rw [hconj, LinearMap.det_conj]
  have : FiniteDimensional ℂ (LinearMap.range Pc) := Module.Finite.equiv e
  obtain ⟨-, halt, -, hU⟩ := g32rep_form_spec X
  refine rfd_det_eq_one_of_alt ((g32rep_form X).compl₁₂ (LinearMap.range Pc).subtype
    (LinearMap.range Pc).subtype) (fun a => halt a) (fun a ha => ?_) _ (fun a b => hU u hu a b)
  apply Subtype.ext
  refine g32rep_primC_nondeg X S (by rw [← hrange]; exact a.2) fun w hw => ?_
  rw [← hrange] at hw
  exact ha ⟨w, hw⟩

/-! ### The supplier determinant identity -/

/-- `e_τ` depends only on the isomorphism class of `τ`. -/
theorem g32rep_char_iso (X : g32p_Cover A) {τ σ : FDRep ℂ g32p_G} (i : τ ≅ σ)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) :
    g32c_char X τ u hu = g32c_char X σ u hu := by
  obtain ⟨L, hLdef⟩ : ∃ L, L = FDRep.isoToLinearEquiv i := ⟨_, rfl⟩
  have hL : ∀ g, (L.symm : σ →ₗ[ℂ] τ) ∘ₗ σ.ρ g = τ.ρ g ∘ₗ (L.symm : σ →ₗ[ℂ] τ) := by
    intro g
    rw [FDRep.Iso.conj_ρ i g, ← hLdef]
    ext x
    simp [LinearEquiv.conj_apply]
  let F : g32c_mult X τ →ₗ[ℂ] g32c_mult X σ :=
    ((LinearMap.lcomp ℂ (ℂ ⊗[ℚ] HQ X.J 1) (L.symm : σ →ₗ[ℂ] τ)).comp
      (g32c_mult X τ).subtype).codRestrict (g32c_mult X σ) fun φ g => by
        change (φ.1 ∘ₗ (L.symm : σ →ₗ[ℂ] τ)) ∘ₗ σ.ρ g = _ ∘ₗ (φ.1 ∘ₗ (L.symm : σ →ₗ[ℂ] τ))
        rw [LinearMap.comp_assoc, hL g, ← LinearMap.comp_assoc, φ.2 g, LinearMap.comp_assoc]
  let G' : g32c_mult X σ →ₗ[ℂ] g32c_mult X τ :=
    ((LinearMap.lcomp ℂ (ℂ ⊗[ℚ] HQ X.J 1) (L : τ →ₗ[ℂ] σ)).comp
      (g32c_mult X σ).subtype).codRestrict (g32c_mult X τ) fun φ g => by
        have hL' : (L : τ →ₗ[ℂ] σ) ∘ₗ τ.ρ g = σ.ρ g ∘ₗ (L : τ →ₗ[ℂ] σ) := by
          rw [FDRep.Iso.conj_ρ i g, ← hLdef]
          ext x
          simp [LinearEquiv.conj_apply]
        change (φ.1 ∘ₗ (L : τ →ₗ[ℂ] σ)) ∘ₗ τ.ρ g = _ ∘ₗ (φ.1 ∘ₗ (L : τ →ₗ[ℂ] σ))
        rw [LinearMap.comp_assoc, hL', ← LinearMap.comp_assoc, φ.2 g, LinearMap.comp_assoc]
  let e : g32c_mult X τ ≃ₗ[ℂ] g32c_mult X σ :=
    LinearEquiv.ofLinearMap F G'
      (LinearMap.ext fun φ => Subtype.ext (LinearMap.ext fun x => by
        change φ.1 (L (L.symm x)) = φ.1 x
        rw [L.apply_symm_apply]))
      (LinearMap.ext fun φ => Subtype.ext (LinearMap.ext fun x => by
        change φ.1 (L.symm (L x)) = φ.1 x
        rw [L.symm_apply_apply]))
  have hconj : g32c_multAct X σ u hu =
      (e : g32c_mult X τ →ₗ[ℂ] g32c_mult X σ) ∘ₗ g32c_multAct X τ u hu ∘ₗ
        (e.symm : g32c_mult X σ →ₗ[ℂ] g32c_mult X τ) :=
    LinearMap.ext fun φ => Subtype.ext (LinearMap.ext fun x => by
      change u (φ.1 x) = u (φ.1 (L (L.symm x)))
      rw [L.apply_symm_apply])
  unfold g32c_char
  rw [hconj, LinearMap.det_conj]

theorem g32rep_selfDual_of_char {V W : FDRep ℂ g32p_G} (h : V.character = W.character)
    (hV : g32p_SelfDual V) : g32p_SelfDual W := fun g => by rw [← h]; exact hV g

theorem g32rep_nontrivial_of_not_selfDual {V : FDRep ℂ g32p_G} (h : ¬ g32p_SelfDual V) :
    ∃ g, V.ρ g ≠ 1 := by
  by_contra hc
  push Not at hc
  refine h fun g => ?_
  change star (LinearMap.trace ℂ V (V.ρ g)) = LinearMap.trace ℂ V (V.ρ g)
  rw [hc g, LinearMap.trace_one, Complex.star_def, Complex.conj_natCast]

theorem g32rep_nontrivial_of_quaternionic {V : FDRep ℂ g32p_G} (h : g32p_Quaternionic V) :
    ∃ g, V.ρ g ≠ 1 := by
  by_contra hc
  push Not at hc
  have h2 := h.2
  have hch : ∀ g, V.character (g * g) = (Module.finrank ℂ V : ℂ) := fun g => by
    change LinearMap.trace ℂ V (V.ρ (g * g)) = _
    rw [hc, LinearMap.trace_one]
  simp only [hch, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  have hc0 : (Fintype.card g32p_G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have : (Fintype.card g32p_G : ℂ) * ((Module.finrank ℂ V : ℂ) + 1) = 0 := by
    rw [mul_add, mul_one, h2, neg_add_cancel]
  rcases mul_eq_zero.1 this with h0 | h0
  · exact hc0 h0
  · have : ((Module.finrank ℂ V + 1 : ℕ) : ℂ) = 0 := by push_cast; exact h0
    exact Nat.succ_ne_zero _ (Nat.cast_eq_zero.1 this)

theorem g32rep_char_eq_one_of_bot (X : g32p_Cover A) {σ : FDRep ℂ g32p_G}
    (h : g32c_mult X σ = ⊥) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) :
    g32c_char X σ u hu = 1 := by
  have : Subsingleton (g32c_mult X σ) := by
    rw [h]
    infer_instance
  exact LinearMap.det_eq_one_of_subsingleton _

/-- **The supplier determinant.** On the `(H, ψ)`-eigenspace, `u ∈ U` has determinant
`charOf(a(ψ))`. -/
theorem g32rep_det_eigen_charOf (X : g32p_Cover A) {I K : Type*} [Fintype I] [Fintype K]
    (τ τbar : I → FDRep ℂ g32p_G) (θ : K → FDRep ℂ g32p_G) (hE : g32c_Enumeration τ τbar θ)
    (H : Subgroup g32p_G) (ψ : H →* ℂˣ) (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1))
    (hu : u ∈ g32c_U X) :
    LinearMap.det (rfd_eigenAct (g32rep_rep X) H ψ u (g32rep_U_le X hu)) =
      g32c_charOf X τ θ u hu (papersA τ τbar θ H ψ) := by
  classical
  have := (torusCohomology_cupProductOf X.J).finite
  obtain ⟨Idx, _, σ, hσ, hdist, hcov⟩ := rfd_simple_family g32p_G
  rw [rfd_det_eigen σ (g32rep_rep X) hσ hdist hcov H ψ u (g32rep_U_le X hu)]
  simp only [rfd_finrank_eigen_eq_papersMult_aux]
  change ∏ j, g32c_char X (σ j) u hu ^ papersMult H (σ j) ψ = _
  have charEq : ∀ {V W : FDRep ℂ g32p_G}, Nonempty (V ≅ W) → V.character = W.character :=
    fun ⟨e⟩ => FDRep.char_iso e
  have hτsd : ∀ i, ¬ g32p_SelfDual (τ i) := fun i => (hE.1 i).2.2.1
  have hbar : ∀ i, (τbar i).character = fun g => star ((τ i).character g) :=
    fun i => funext (hE.1 i).2.2.2.1
  have hbsd : ∀ i, ¬ g32p_SelfDual (τbar i) := fun i hsd => hτsd i fun g => by
    have := hsd g
    rw [hbar i] at this
    simp only [star_star] at this
    exact this.symm
  choose jτ hjτ using fun i => hcov (τ i) (hE.1 i).1
  choose jb hjb using fun i => hcov (τbar i) (hE.1 i).2.1
  choose jθ hjθ using fun q => hcov (θ q) (hE.2.1 q).1
  have hτinj : ∀ i i', Nonempty (τ i ≅ τ i') → i = i' := fun i i' ⟨e⟩ => by
    by_contra hne
    exact (hE.2.2.1 i i' hne).1.false e
  have injτ : Function.Injective jτ := fun i i' h => by
    obtain ⟨e1⟩ := hjτ i
    obtain ⟨e2⟩ := hjτ i'
    exact hτinj i i' ⟨e1 ≪≫ eqToIso (congrArg σ h) ≪≫ e2.symm⟩
  have injb : Function.Injective jb := fun i i' h => by
    obtain ⟨e1⟩ := hjb i
    obtain ⟨e2⟩ := hjb i'
    have hc := FDRep.char_iso (e1 ≪≫ eqToIso (congrArg σ h) ≪≫ e2.symm)
    rw [hbar i, hbar i'] at hc
    have hc' : (τ i).character = (τ i').character := funext fun g => by
      exact star_injective (congrFun hc g)
    have := (hE.1 i).1
    have := (hE.1 i').1
    exact hτinj i i' (rfd_iso_of_character_eq _ _ hc')
  have injθ : Function.Injective jθ := fun q q' h => by
    obtain ⟨e1⟩ := hjθ q
    obtain ⟨e2⟩ := hjθ q'
    by_contra hne
    exact (hE.2.2.2.1 q q' hne).false (e1 ≪≫ eqToIso (congrArg σ h) ≪≫ e2.symm)
  have dτb : ∀ i i', jτ i ≠ jb i' := fun i i' h => by
    obtain ⟨e1⟩ := hjτ i
    obtain ⟨e2⟩ := hjb i'
    have e : τ i ≅ τbar i' := e1 ≪≫ eqToIso (congrArg σ h) ≪≫ e2.symm
    by_cases hii : i = i'
    · subst hii
      refine hτsd i fun g => ?_
      have := congrFun (FDRep.char_iso e) g
      rw [hbar i] at this
      exact this.symm
    · exact (hE.2.2.1 i i' hii).2.false e
  have dτθ : ∀ i q, jτ i ≠ jθ q := fun i q h => by
    obtain ⟨e1⟩ := hjτ i
    obtain ⟨e2⟩ := hjθ q
    exact hτsd i (g32rep_selfDual_of_char
      (FDRep.char_iso (e1 ≪≫ eqToIso (congrArg σ h) ≪≫ e2.symm)).symm (hE.2.1 q).2.1.1)
  have dbθ : ∀ i q, jb i ≠ jθ q := fun i q h => by
    obtain ⟨e1⟩ := hjb i
    obtain ⟨e2⟩ := hjθ q
    exact hbsd i (g32rep_selfDual_of_char
      (FDRep.char_iso (e1 ≪≫ eqToIso (congrArg σ h) ≪≫ e2.symm)).symm (hE.2.1 q).2.1.1)
  have hrest : ∀ j, (∀ i, jτ i ≠ j) → (∀ i, jb i ≠ j) → (∀ q, jθ q ≠ j) →
      g32c_char X (σ j) u hu = 1 := by
    intro j h1 h2 h3
    have hσj := hσ j
    by_cases hsd : g32p_SelfDual (σ j)
    · by_cases hq : g32p_Quaternionic (σ j)
      · by_cases hcw : 0 < g32p_cwMult (σ j)
        · obtain ⟨q, ⟨e⟩⟩ := (hE.2.2.2.2 (σ j) hσj hcw).2 hq
          obtain ⟨e2⟩ := hjθ q
          exact absurd (hdist j (jθ q) ⟨e ≪≫ e2⟩).symm (h3 q)
        · exact g32rep_char_eq_one_of_bot X (g32rep_mult_eq_bot X (σ j) hσj
            (g32rep_nontrivial_of_quaternionic hq) (not_lt.1 hcw)) u hu
      · exact g32rep_orthogonal X (σ j) hσj hsd hq u hu
    · by_cases hcw : 0 < g32p_cwMult (σ j)
      · obtain ⟨i, hi | hi⟩ := (hE.2.2.2.2 (σ j) hσj hcw).1 hsd
        · obtain ⟨e⟩ := hi
          obtain ⟨e2⟩ := hjτ i
          exact absurd (hdist j (jτ i) ⟨e ≪≫ e2⟩).symm (h1 i)
        · obtain ⟨e⟩ := hi
          obtain ⟨e2⟩ := hjb i
          exact absurd (hdist j (jb i) ⟨e ≪≫ e2⟩).symm (h2 i)
      · exact g32rep_char_eq_one_of_bot X (g32rep_mult_eq_bot X (σ j) hσj
          (g32rep_nontrivial_of_not_selfDual hsd) (not_lt.1 hcw)) u hu
  set F : Idx → ℂ := fun j => g32c_char X (σ j) u hu ^ papersMult H (σ j) ψ with hF
  let A := Finset.univ.image jτ
  let B := Finset.univ.image jb
  let C := Finset.univ.image jθ
  have hAB : Disjoint A B := Finset.disjoint_left.2 fun j hA hB => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨i', -, hi'⟩ := Finset.mem_image.1 hB
    exact dτb i i' hi'.symm
  have hABC : Disjoint (A ∪ B) C := Finset.disjoint_left.2 fun j hAB hC => by
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hC
    rcases Finset.mem_union.1 hAB with hA | hB
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hA
      exact dτθ i q hi
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hB
      exact dbθ i q hi
  have hsplit : ∏ j, F j = ∏ j ∈ A ∪ B ∪ C, F j := by
    rw [← Finset.prod_sdiff (Finset.subset_univ (A ∪ B ∪ C))]
    rw [Finset.prod_eq_one, one_mul]
    intro j hj
    have hj' := (Finset.mem_sdiff.1 hj).2
    have h1 : ∀ i, jτ i ≠ j := fun i h => hj' (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩)))
    have h2 : ∀ i, jb i ≠ j := fun i h => hj' (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩)))
    have h3 : ∀ q, jθ q ≠ j := fun q h => hj' (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨q, Finset.mem_univ _, h⟩))
    rw [hF]
    dsimp only
    rw [hrest j h1 h2 h3, one_pow]
  have hA : ∏ j ∈ A, F j = ∏ i, g32c_char X (τ i) u hu ^ papersMult H (τ i) ψ := by
    rw [Finset.prod_image fun i _ i' _ h => injτ h]
    refine Finset.prod_congr rfl fun i _ => ?_
    obtain ⟨e⟩ := hjτ i
    rw [hF]
    dsimp only
    rw [g32rep_char_iso X e.symm, rfd_papersMult_iso H e.symm]
  have hB : ∏ j ∈ B, F j = ∏ i, (g32c_char X (τ i) u hu)⁻¹ ^ papersMult H (τbar i) ψ := by
    rw [Finset.prod_image fun i _ i' _ h => injb h]
    refine Finset.prod_congr rfl fun i _ => ?_
    obtain ⟨e⟩ := hjb i
    rw [hF]
    dsimp only
    rw [g32rep_char_iso X e.symm, rfd_papersMult_iso H e.symm,
      eq_inv_of_mul_eq_one_left (g32rep_conj X τ τbar θ hE i u hu)]
  have hC : ∏ j ∈ C, F j =
      ∏ q, g32c_char X (θ q) u hu ^ ((papersMult H (θ q) ψ : ZMod 2)).val := by
    rw [Finset.prod_image fun i _ i' _ h => injθ h]
    refine Finset.prod_congr rfl fun q _ => ?_
    obtain ⟨e⟩ := hjθ q
    rw [hF]
    dsimp only
    rw [g32rep_char_iso X e.symm, rfd_papersMult_iso H e.symm, ZMod.val_natCast]
    have h2 := g32rep_parity X (θ q) (hE.2.1 q).1 (hE.2.1 q).2.1 u hu
    conv_lhs => rw [← Nat.mod_add_div (papersMult H (θ q) ψ) 2, pow_add, pow_mul, h2, one_pow,
      mul_one]
  rw [hsplit, Finset.prod_union hABC, Finset.prod_union hAB, hA, hB, hC, g32c_charOf, papersA,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hne : g32c_char X (τ i) u hu ≠ 0 :=
    right_ne_zero_of_mul_eq_one (g32rep_conj X τ τbar θ hE i u hu)
  rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]

/-! ### Complementary eigenspaces -/

section Complement

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m h : ℕ} [NeZero m]

/-- The eigenspaces of distinct embeddings are independent. -/
theorem g32rep_eigenspace_iSupIndep (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    iSupIndep (cyc_eigenspace e) := by
  let ζ := IsCyclotomicExtension.zeta m ℚ (cyc_Field m)
  have hinj : Function.Injective (fun t : cyc_Field m →ₐ[ℚ] ℂ => t ζ) := by
    intro t s h1
    refine AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top
      (IsCyclotomicExtension.zeta_spec m ℚ (cyc_Field m))) ?_
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact h1
  exact ((Module.End.eigenspaces_iSupIndep ((cyc_scalar e ζ).baseChange ℂ)).comp hinj).mono
    fun t => iInf_le _ ζ

variable [Module.Finite ℚ V]

omit [NeZero m] in
theorem g32rep_finrank_eigenspace (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    Module.finrank ℂ ↥(cyc_eigenspace e t) = h := by
  have h1 := spec_a2a_finrank (cyc_rep e) t
  have h2 : Module.finrank ℚ V = h * Module.finrank ℚ (cyc_Field m) := by
    rw [e.finrank_eq, Module.finrank_pi_fintype]
    simp
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos (h1.trans h2)

theorem g32rep_finrank_field : Module.finrank ℚ (cyc_Field m) = m.totient :=
  IsCyclotomicExtension.finrank (cyc_Field m)
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))

theorem g32rep_finrank_coSum (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    Module.finrank ℂ ↥(⨆ (s) (_ : s ≠ t), cyc_eigenspace e s) = h * (m.totient - 1) := by
  classical
  have hind : iSupIndep fun s : {s : cyc_Field m →ₐ[ℚ] ℂ // s ≠ t} => cyc_eigenspace e s.1 :=
    (g32rep_eigenspace_iSupIndep e).comp Subtype.val_injective
  have e1 : (⨆ (s) (_ : s ≠ t), cyc_eigenspace e s) =
      ⨆ s : {s : cyc_Field m →ₐ[ℚ] ℂ // s ≠ t}, cyc_eigenspace e s.1 := iSup_subtype'
  rw [e1, Submodule.iSup_eq_range_dfinsupp_lsum,
    LinearMap.finrank_range_of_inj hind.dfinsupp_lsum_injective]
  have e2 : Module.finrank ℂ (Π₀ s : {s : cyc_Field m →ₐ[ℚ] ℂ // s ≠ t},
      ↥(cyc_eigenspace e s.1)) = ∑ s : {s : cyc_Field m →ₐ[ℚ] ℂ // s ≠ t},
        Module.finrank ℂ ↥(cyc_eigenspace e s.1) :=
    Module.finrank_directSum ℂ _
  rw [e2]
  simp only [g32rep_finrank_eigenspace, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hcard : Fintype.card {s : cyc_Field m →ₐ[ℚ] ℂ // s ≠ t} = m.totient - 1 := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, AlgHom.card ℚ (cyc_Field m) ℂ, g32rep_finrank_field]
  rw [hcard, mul_comm]

theorem g32rep_isCompl_coSum (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    IsCompl (cyc_eigenspace e t) (⨆ (s) (_ : s ≠ t), cyc_eigenspace e s) := by
  have hd := g32rep_eigenspace_iSupIndep e t
  refine ⟨hd, codisjoint_iff.2 (Submodule.eq_top_of_finrank_eq ?_)⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (cyc_eigenspace e t)
    (⨆ (s) (_ : s ≠ t), cyc_eigenspace e s)
  rw [disjoint_iff.1 hd, finrank_bot, add_zero, g32rep_finrank_eigenspace, g32rep_finrank_coSum] at h1
  rw [h1, Module.finrank_baseChange, e.finrank_eq, Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, g32rep_finrank_field]
  have : 1 ≤ m.totient := Nat.totient_pos.2 (NeZero.pos m)
  rw [Nat.mul_sub, mul_one, Nat.add_sub_cancel' (Nat.le_mul_of_pos_right h this)]

end Complement

/-- The transport preserves every eigenspace `V_s`. -/
theorem g32rep_restrict_mem_eigen (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X)
    (s : cyc_Field S.m →ₐ[ℚ] ℂ) (y : ℂ ⊗[ℚ] HQ (X.part S hS).P 1)
    (hy : y ∈ cyc_eigenspace (X.part S hS).act.cyc_coordinates s) :
    g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u y ∈
      cyc_eigenspace (X.part S hS).act.cyc_coordinates s := by
  simp only [cyc_eigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hy ⊢
  intro a
  rw [← LinearMap.comp_apply, ← g32rep_restrict_cyc_aux X S hS hu a, LinearMap.comp_apply, hy a,
    map_smul]

theorem g32rep_hco_aux (X : g32p_Cover A) (S : g32p_Supplier) (hS : g32p_Admissible X.aut S)
    (χc : S.H →* ℂˣ)
    (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)
    {I K : Type*} [Fintype I] [Fintype K] (τ τbar : I → FDRep ℂ g32p_G)
    (θ : K → FDRep ℂ g32p_G) (hE : g32c_Enumeration τ τbar θ) :
    ∀ (k : ℤ) (t : cyc_Field S.m →ₐ[ℚ] ℂ), t (g32p_zeta S) = g32p_root S.m ^ k →
      ∀ (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X),
      ∀ Z ∈ g32c_coLine (X.part S hS).act.cyc_coordinates t
          (2 * (X.part S hS).k * (S.m.totient - 1)),
        exteriorPower.map (2 * (X.part S hS).k * (S.m.totient - 1))
            (g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u) Z =
          (g32c_charOf X τ θ u hu (papersA τ τbar θ S.H (χc ^ k)))⁻¹ • Z := by
  intro k t ht u hu Z hZ
  let := (torusCohomology_cupProductOf (X.part S hS).P).finite
  set e := (X.part S hS).act.cyc_coordinates with he
  set R := g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u with hR
  set U := ⨆ (s) (_ : s ≠ t), cyc_eigenspace e s with hU
  have hRV : ∀ y ∈ cyc_eigenspace e t, R y ∈ cyc_eigenspace e t :=
    g32rep_restrict_mem_eigen X S hS hu t
  have hRU : ∀ y ∈ U, R y ∈ U := by
    have hle : U ≤ U.comap R := iSup₂_le fun s hs y hy =>
      Submodule.mem_comap.2 ((le_iSup₂ (f := fun s (_ : s ≠ t) => cyc_eigenspace e s) s hs)
        (g32rep_restrict_mem_eigen X S hS hu s y hy))
    exact fun y hy => hle hy
  have hfinU : Module.finrank ℂ U = 2 * (X.part S hS).k * (S.m.totient - 1) :=
    g32rep_finrank_coSum e t
  obtain ⟨z, rfl⟩ := hZ
  have hcomp : R ∘ₗ U.subtype = U.subtype ∘ₗ R.restrict hRU := rfl
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hcomp, exteriorPower.map_comp,
    LinearMap.comp_apply, rfd_exteriorPower_map_top hfinU, map_smul]
  congr 1
  -- the determinant on `V_t`
  have hVt : LinearMap.det (R.restrict hRV) = g32c_charOf X τ θ u hu (papersA τ τbar θ S.H (χc ^ k)) := by
    rw [← g32rep_det_eigen_charOf X τ τbar θ hE S.H (χc ^ k) u hu]
    set Pc := (homPullback (X.part S hS).proj 1).baseChange ℂ
    let E : cyc_eigenspace e t ≃ₗ[ℂ] rfd_eigen (g32rep_rep X) S.H (χc ^ k) :=
      (Submodule.equivMapOfInjective Pc (g32rep_proj_injective X S hS) _).trans
        (LinearEquiv.ofEq _ _ (g32rep_proj_eigen_aux X S hS χc hχc k t ht))
    have hconj : rfd_eigenAct (g32rep_rep X) S.H (χc ^ k) u (g32rep_U_le X hu) =
        (E : _ →ₗ[ℂ] _) ∘ₗ R.restrict hRV ∘ₗ (E.symm : _ →ₗ[ℂ] _) := by
      refine LinearMap.ext fun w => ?_
      obtain ⟨y, rfl⟩ := E.surjective w
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      change u (Pc y) = Pc (R y)
      exact (LinearMap.congr_fun (g32rep_restrict_proj_aux X S hS hu) y).symm
    rw [hconj, LinearMap.det_conj]
  have hdet := rfd_det_eq_mul_of_isCompl R (g32rep_isCompl_coSum e t) hRV hRU
  rw [g32rep_det_restrict_aux X S hS hu, hVt] at hdet
  exact eq_inv_of_mul_eq_one_right hdet.symm

end HodgeLean.Foundations.Program
