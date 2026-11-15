import HodgeLean.Foundations.Program.G32ContractionDefs

/-! # Reduction of the `U`-invariance of `Γ`

The action of a family of factor endomorphisms on `g32c_gammaAbs`, nonvanishing and isomorphism
invariance of the characters `e_τ`, the sign swap of `papersA` under complex conjugation, and the
character sum of the identity `e_ρ = Σ_j ε_j a(χ_j)`. Together they reduce the `U`-invariance of
`Γ` to the character of the Weil line, the characters of the complementary lines and the parity
`e_θ² = 1` of the quaternionic coordinates (`g32c_gamma_invariant_of`). HC no distance; AV
milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

section Factor

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {r : ℕ} {N : Fin r → Type*}
  [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)]

theorem g32c_map_map {P Q R : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]
    [AddCommGroup R] [Module ℂ R] (f : P →ₗ[ℂ] Q) (g : Q →ₗ[ℂ] R) (x : ExteriorAlgebra ℂ P) :
    ExteriorAlgebra.map g (ExteriorAlgebra.map f x) = ExteriorAlgebra.map (g ∘ₗ f) x := by
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]

theorem g32c_factorAction_gammaAbs (uM : Module.End ℂ M) (uN : ∀ j, Module.End ℂ (N j))
    (w : ExteriorAlgebra ℂ M) (Z : ∀ j, ExteriorAlgebra ℂ (N j)) :
    g32c_factorAction uM uN (g32c_gammaAbs w Z) =
      g32c_gammaAbs (ExteriorAlgebra.map uM w) fun j => ExteriorAlgebra.map (uN j) (Z j) := by
  simp only [g32c_factorAction, g32c_gammaAbs, map_mul, map_list_prod, List.map_ofFn]
  congr 1
  · rw [g32c_map_map, g32c_map_map]
    congr 1
    ext x
    simp
  · congr 1
    congr 1
    funext j
    simp only [Function.comp_apply]
    rw [g32c_map_map, g32c_map_map]
    congr 2
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.inr_apply,
      LinearMap.coe_single, map_zero, Prod.mk.injEq, true_and]
    funext i
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    exact Pi.apply_single (fun i => uN i) (fun i => map_zero _) j x i

theorem g32c_prod_ofFn_smul {B : Type*} [Ring B] [Algebra ℂ B] :
    ∀ (n : ℕ) (d : Fin n → ℂ) (x : Fin n → B),
      (List.ofFn fun j => d j • x j).prod = (∏ j, d j) • (List.ofFn x).prod
  | 0, _, _ => by simp
  | n + 1, d, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      g32c_prod_ofFn_smul n (fun j => d j.succ) (fun j => x j.succ), smul_mul_smul_comm,
      Fin.prod_univ_succ]

theorem g32c_gammaAbs_smul (a : ℂ) (b : Fin r → ℂ) (w : ExteriorAlgebra ℂ M)
    (Z : ∀ j, ExteriorAlgebra ℂ (N j)) :
    g32c_gammaAbs (a • w) (fun j => b j • Z j) = (a * ∏ j, b j) • g32c_gammaAbs w Z := by
  simp only [g32c_gammaAbs, map_smul]
  rw [g32c_prod_ofFn_smul r b, smul_mul_smul_comm]

end Factor

theorem g32c_prod_zpow {α G : Type*} [CommGroup G] (g : G) (n : α → ℤ) (s : Finset α) :
    ∏ j ∈ s, g ^ n j = g ^ ∑ j ∈ s, n j := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add]

variable {A : g32t_Sixfold}

section Character

theorem g32c_char_ne_zero (X : g32p_Cover A) (τ : FDRep ℂ g32p_G)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) : g32c_char X τ u hu ≠ 0 := by
  obtain ⟨v, rfl⟩ := hu.1
  let B : g32p_G → Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1) := fun g =>
    (homPullback (X.aut g) 1).baseChange ℂ
  have hcomm : ∀ g, (↑v⁻¹ : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) ∘ₗ B g = B g ∘ₗ ↑v⁻¹ := fun g =>
    (Commute.units_inv_left (hu.2.1 g : Commute (↑v : Module.End ℂ _) (B g))).eq
  let w : Module.End ℂ (g32c_mult X τ) :=
    (LinearMap.compRight ℂ (↑v⁻¹ : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1))).restrict fun φ hφ g => by
      change ((↑v⁻¹ : Module.End ℂ _) ∘ₗ φ) ∘ₗ τ.ρ g = _ ∘ₗ ((↑v⁻¹ : Module.End ℂ _) ∘ₗ φ)
      rw [LinearMap.comp_assoc, hφ g, ← LinearMap.comp_assoc, hcomm g, LinearMap.comp_assoc]
  have h1 : g32c_multAct X τ (↑v) hu * w = 1 := by
    refine LinearMap.ext fun φ => Subtype.ext (LinearMap.ext fun x => ?_)
    change (↑v : Module.End ℂ _) ((↑v⁻¹ : Module.End ℂ _) (φ.1 x)) = φ.1 x
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  have h2 := congrArg LinearMap.det h1
  rw [map_mul, map_one] at h2
  exact left_ne_zero_of_mul_eq_one h2

theorem g32c_char_iso (X : g32p_Cover A) {τ σ : FDRep ℂ g32p_G} (i : τ ≅ σ)
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

end Character

section Sign

theorem g32c_supplier_pow_m (S : g32p_Supplier) (χc : S.H →* ℂˣ)
    (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)
    (h : S.H) : ((χc h : ℂˣ) : ℂ) ^ S.m = 1 := by
  rw [hχc, ← pow_mul, mul_comm, pow_mul, g32p_root,
    (Complex.isPrimitiveRoot_exp S.m (NeZero.ne _)).pow_eq_one, one_pow]

theorem g32c_supplier_inv (S : g32p_Supplier) (χc : S.H →* ℂˣ)
    (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)
    (h : S.H) : ((χc h : ℂˣ) : ℂ)⁻¹ = ((χc h : ℂˣ) : ℂ) ^ (S.m - 1) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ', Nat.sub_add_cancel (NeZero.one_le), g32c_supplier_pow_m S χc hχc h]

theorem g32c_papersA_inv (S : g32p_Supplier) (χc : S.H →* ℂˣ)
    (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)
    {I K : Type*} (τ τbar : I → FDRep ℂ g32p_G) (θ : K → FDRep ℂ g32p_G)
    (hE : g32c_Enumeration τ τbar θ) :
    papersA τ τbar θ S.H (χc ^ (-1 : ℤ)) =
      (-(papersA τ τbar θ S.H χc).1, (papersA τ τbar θ S.H χc).2) := by
  classical
  have : Fintype S.H := Fintype.ofFinite S.H
  have hinv : χc ^ (-1 : ℤ) = χc ^ (S.m - 1) := by
    refine MonoidHom.ext fun h => Units.ext ?_
    rw [zpow_neg_one, MonoidHom.inv_apply, MonoidHom.pow_apply, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val, g32c_supplier_inv S χc hχc h]
  have hγ : ∀ h, starRingEnd ℂ ((χc h : ℂˣ) : ℂ) = ((χc h : ℂˣ) : ℂ) ^ (S.m - 1) := by
    intro h
    rw [← g32c_supplier_inv S χc hχc h, Complex.inv_eq_conj
      (Complex.norm_eq_one_of_pow_eq_one (g32c_supplier_pow_m S χc hχc h) (NeZero.ne _))]
  have hsw := papers_g32_sign_swap τ τbar θ S.H (starRingEnd ℂ) χc (S.m - 1) hγ
    (fun i g => by rw [starRingEnd_apply]; exact ((hE.1 i).2.2.2.1 g).symm)
    (fun i g => by rw [starRingEnd_apply, (hE.1 i).2.2.2.1 g, star_star])
    (fun q g => by rw [starRingEnd_apply]; exact (hE.2.1 q).2.1.1 g)
  rw [hinv]
  exact Prod.ext hsw.1 hsw.2

theorem g32c_papersA_units (S : g32p_Supplier) (χc : S.H →* ℂˣ)
    (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)
    {I K : Type*} (τ τbar : I → FDRep ℂ g32p_G) (θ : K → FDRep ℂ g32p_G)
    (hE : g32c_Enumeration τ τbar θ) (n : ℤˣ) :
    papersA τ τbar θ S.H (χc ^ (n : ℤ)) =
      ((n : ℤ) • (papersA τ τbar θ S.H χc).1, (papersA τ τbar θ S.H χc).2) := by
  rcases Int.units_eq_one_or n with rfl | rfl
  · simp
  · rw [Units.val_neg, Units.val_one, g32c_papersA_inv S χc hχc τ τbar θ hE, neg_one_smul]

end Sign

section Sum

theorem g32c_charOf_prod (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (χc : ∀ j, (S j).H →* ℂˣ)
    (hχc : ∀ j h, ((χc j h : ℂˣ) : ℂ) =
      g32p_root (S j).m ^ (Multiplicative.toAdd ((S j).χ h)).val)
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] (τ τbar : I → FDRep ℂ g32p_G)
    (θ : K → FDRep ℂ g32p_G) (hE : g32c_Enumeration τ τbar θ) (iρ : I)
    (hρ : Nonempty (τ iρ ≅ g32p_rho)) (ε : Fin r → ℤˣ)
    (hid : ∑ j, (ε j : ℤ) • papersA τ τbar θ (S j).H (χc j) = (Pi.single iρ 1, 0))
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X)
    (hpar : ∀ q, g32c_char X (θ q) u hu ^ 2 = 1) (δ : ℤˣ) :
    ∏ j, g32c_charOf X τ θ u hu (papersA τ τbar θ (S j).H (χc j ^ ((δ * ε j : ℤˣ) : ℤ))) =
      g32c_char X g32p_rho u hu ^ (δ : ℤ) := by
  classical
  let e : I → ℂˣ := fun i => Units.mk0 _ (g32c_char_ne_zero X (τ i) u hu)
  let f : K → ℂˣ := fun q => Units.mk0 _ (g32c_char_ne_zero X (θ q) u hu)
  let a : Fin r → (I → ℤ) × (K → ZMod 2) := fun j => papersA τ τbar θ (S j).H (χc j)
  have hco : ∀ b : (I → ℤ) × (K → ZMod 2), g32c_charOf X τ θ u hu b =
      (((∏ i, e i ^ b.1 i) * ∏ q, f q ^ (b.2 q).val : ℂˣ) : ℂ) := by
    intro b
    simp [g32c_charOf, e, f, Units.val_zpow_eq_zpow_val]
  have h1 : ∀ i, ∑ j, (ε j : ℤ) * (a j).1 i = (Pi.single iρ 1 : I → ℤ) i := by
    intro i
    have := congrFun (congrArg Prod.fst hid) i
    simpa [Prod.fst_sum, Finset.sum_apply] using this
  have h2 : ∀ q, ∑ j, (a j).2 q = 0 := by
    intro q
    have := congrFun (congrArg Prod.snd hid) q
    simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply,
      Pi.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases Int.units_eq_one_or (ε j) with h | h
    · rw [h, Units.val_one, one_smul]
    · rw [h, Units.val_neg, Units.val_one, neg_one_smul, ZMod.neg_eq_self_mod_two]
  have hf : ∀ q, ∏ j, f q ^ ((a j).2 q).val = 1 := by
    intro q
    rw [Finset.prod_pow_eq_pow_sum]
    have hdvd : 2 ∣ ∑ j, ((a j).2 q).val := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
      simp only [ZMod.natCast_zmod_val]
      exact h2 q
    obtain ⟨c, hc⟩ := hdvd
    have hf2 : f q ^ 2 = 1 := Units.ext (by simpa [f] using hpar q)
    rw [hc, pow_mul, hf2, one_pow]
  have he : ∏ i, e i ^ ∑ j, ((δ * ε j : ℤˣ) : ℤ) * (a j).1 i = e iρ ^ (δ : ℤ) := by
    rw [Finset.prod_eq_single iρ]
    · congr 1
      rw [← mul_one (δ : ℤ), ← Pi.single_eq_same (M := fun _ => ℤ) iρ 1, ← h1 iρ,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Units.val_mul, mul_assoc]
    · intro i _ hi
      have : ∑ j, ((δ * ε j : ℤˣ) : ℤ) * (a j).1 i = 0 := by
        have h0 := h1 i
        rw [Pi.single_eq_of_ne hi] at h0
        simp_rw [Units.val_mul, mul_assoc, ← Finset.mul_sum, h0, mul_zero]
      rw [this, zpow_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp_rw [hco, g32c_papersA_units _ _ (hχc _) τ τbar θ hE]
  rw [← Units.coe_prod]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  rw [Finset.prod_comm, Finset.prod_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun j q => f q ^ ((a j).2 q).val)]
  simp_rw [g32c_prod_zpow, hf, Finset.prod_const_one, mul_one]
  rw [he, Units.val_zpow_eq_zpow_val, Units.val_mk0, g32c_char_iso X hρ.some u hu]

end Sum

/-- **Reduction of the `U`-invariance of `Γ`.** Statement 5 of the stage follows from three
inputs: the character `e_ρ^ε` of the Weil line (the conclusion of `g32c_weil_character`), the
parity `e_θ² = 1` of the quaternionic characters, and the character `charOf(a(χ^k))⁻¹` of `U` on
the complementary line `det(⊕_{s ≠ t} V_s)` of each part for `t(ζ) = exp(2πi/m)^k`. The sign `δ`
is the sign of the Weil line.
Source: G32 v0.16, proof of Proposition 4.6, paragraphs "The correspondence" and "Degrees";
Lemma 4.4 (`papers_g32_sign_swap`). -/
theorem g32c_gamma_invariant_of (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) (χc : ∀ j, (S j).H →* ℂˣ)
    (hχc : ∀ j h, ((χc j h : ℂˣ) : ℂ) =
      g32p_root (S j).m ^ (Multiplicative.toAdd ((S j).χ h)).val)
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] (τ τbar : I → FDRep ℂ g32p_G)
    (θ : K → FDRep ℂ g32p_G) (hE : g32c_Enumeration τ τbar θ) (iρ : I)
    (hρ : Nonempty (τ iρ ≅ g32p_rho)) (ε : Fin r → ℤˣ)
    (hid : ∑ j, (ε j : ℤ) • papersA τ τbar θ (S j).H (χc j) = (Pi.single iρ 1, 0))
    (hW : ∃ ε : ℤˣ, ∀ (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X),
      ∀ z ∈ LinearMap.range (exteriorPower.map 6 A.W.Vs.subtype),
        exteriorPower.map 6 (g32c_restrict X.inclA X.projA X.NA u) z =
          g32c_char X g32p_rho u hu ^ (ε : ℤ) • z)
    (hpar : ∀ (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) (q : K),
      g32c_char X (θ q) u hu ^ 2 = 1)
    (hco : ∀ (j : Fin r) (k : ℤ) (t : cyc_Field (S j).m →ₐ[ℚ] ℂ),
      t (g32p_zeta (S j)) = g32p_root (S j).m ^ k →
      ∀ (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X),
      ∀ Z ∈ g32c_coLine (X.part (S j) (hS j)).act.cyc_coordinates t
          (2 * (X.part (S j) (hS j)).k * ((S j).m.totient - 1)),
        exteriorPower.map (2 * (X.part (S j) (hS j)).k * ((S j).m.totient - 1))
            (g32c_restrict (X.part (S j) (hS j)).incl (X.part (S j) (hS j)).proj
              (X.part (S j) (hS j)).N u) Z =
          (g32c_charOf X τ θ u hu (papersA τ τbar θ (S j).H (χc j ^ k)))⁻¹ • Z) :
    ∃ δ : ℤˣ, ∀ t : ∀ j, cyc_Field (S j).m →ₐ[ℚ] ℂ,
      (∀ j, t j (g32p_zeta (S j)) = g32p_root (S j).m ^ ((δ * ε j : ℤˣ) : ℤ)) →
      ∀ w ∈ LinearMap.range (exteriorPower.map 6 A.W.Vs.subtype),
      ∀ Z : ∀ j, ⋀[ℂ]^(2 * (X.part (S j) (hS j)).k * ((S j).m.totient - 1))
          (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1),
      (∀ j, Z j ∈ g32c_coLine (X.part (S j) (hS j)).act.cyc_coordinates (t j)
          (2 * (X.part (S j) (hS j)).k * ((S j).m.totient - 1))) →
      ∀ u ∈ g32c_U X,
        g32c_factorAction (g32c_restrict X.inclA X.projA X.NA u)
            (fun j => g32c_restrict (X.part (S j) (hS j)).incl (X.part (S j) (hS j)).proj
              (X.part (S j) (hS j)).N u)
            (g32c_gammaAbs (w : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ A.X 1))
              fun j => (Z j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))) =
          g32c_gammaAbs (w : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ A.X 1))
            fun j => (Z j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1)) := by
  obtain ⟨δ, hδ⟩ := hW
  refine ⟨δ, fun t ht w hw Z hZ u hu => ?_⟩
  rw [g32c_factorAction_gammaAbs]
  have hwA : ExteriorAlgebra.map (g32c_restrict X.inclA X.projA X.NA u)
      (w : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ A.X 1)) =
        g32c_char X g32p_rho u hu ^ (δ : ℤ) • (w : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ A.X 1)) := by
    rw [← exteriorPower.coe_map, hδ u hu w hw]
    rfl
  have hZj : (fun j => ExteriorAlgebra.map (g32c_restrict (X.part (S j) (hS j)).incl
      (X.part (S j) (hS j)).proj (X.part (S j) (hS j)).N u)
        (Z j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1))) =
      fun j => (g32c_charOf X τ θ u hu
        (papersA τ τbar θ (S j).H (χc j ^ ((δ * ε j : ℤˣ) : ℤ))))⁻¹ •
          (Z j : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] HQ (g32c_parts X S hS j) 1)) := by
    funext j
    rw [← exteriorPower.coe_map, hco j _ (t j) (ht j) u hu (Z j) (hZ j)]
    rfl
  rw [hwA, hZj, g32c_gammaAbs_smul, Finset.prod_inv_distrib,
    g32c_charOf_prod X S χc hχc τ τbar θ hE iρ hρ ε hid u hu (hpar u hu) δ,
    mul_inv_cancel₀ (zpow_ne_zero _ (g32c_char_ne_zero X g32p_rho u hu)), one_smul]

end HodgeLean.Foundations.Program
