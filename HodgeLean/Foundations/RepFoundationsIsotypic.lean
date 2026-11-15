import HodgeLean.Foundations.RepFoundationsCharacters

/-! # Representation foundations: the isotypic decomposition

Minimal nonzero subrepresentations, Maschke complements, and the bijectivity of the evaluation
map `⊕_i σ_i ⊗ Hom_G(σ_i, V) → V` for a family of simple representations that is pairwise
non-isomorphic and represents every simple isomorphism class.
-/

noncomputable section

namespace HodgeLean.Foundations

open CategoryTheory
open scoped TensorProduct

variable {G : Type} [Group G] [Fintype G]

section Minimal

variable {X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]

omit [FiniteDimensional ℂ X] in
/-- Maschke: a subrepresentation has a complementary subrepresentation. -/
theorem rfd_exists_compl (π : Representation ℂ G X) (P : Subrepresentation π) :
    ∃ Q : Subrepresentation π, IsCompl P.toSubmodule Q.toSubmodule := by
  have : NeZero (Nat.card G : ℂ) := ⟨by simp⟩
  obtain ⟨Q, hQ⟩ := exists_isCompl P
  refine ⟨Q, ⟨?_, ?_⟩⟩
  · rw [disjoint_iff]
    have := congrArg Subrepresentation.toSubmodule hQ.inf_eq_bot
    exact this
  · rw [codisjoint_iff]
    have := congrArg Subrepresentation.toSubmodule hQ.sup_eq_top
    exact this

omit [Fintype G] in
/-- A nonzero subrepresentation contains a minimal nonzero subrepresentation. -/
theorem rfd_exists_minimal (π : Representation ℂ G X) (P : Subrepresentation π)
    (hP : P.toSubmodule ≠ ⊥) :
    ∃ W : Subrepresentation π, W.toSubmodule ≤ P.toSubmodule ∧
      W.toSubmodule ≠ ⊥ ∧ ∀ U : Subrepresentation π,
        U.toSubmodule ≤ W.toSubmodule → U.toSubmodule ≠ ⊥ → U.toSubmodule = W.toSubmodule := by
  induction hn : Module.finrank ℂ P.toSubmodule using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    by_cases h : ∀ U : Subrepresentation π, U.toSubmodule ≤ P.toSubmodule →
        U.toSubmodule ≠ ⊥ → U.toSubmodule = P.toSubmodule
    · exact ⟨P, le_rfl, hP, h⟩
    · push Not at h
      obtain ⟨U, hUP, hU0, hUne⟩ := h
      have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hUP hUne)
      obtain ⟨W, hWU, hW0, hW⟩ := ih _ (hn ▸ hlt) U hU0 rfl
      exact ⟨W, hWU.trans hUP, hW0, hW⟩

/-- A minimal nonzero subrepresentation is a simple object of `FDRep ℂ G`. -/
theorem rfd_simple_of_minimal (π : Representation ℂ G X) (W : Subrepresentation π)
    (hW0 : W.toSubmodule ≠ ⊥)
    (hW : ∀ U : Subrepresentation π,
        U.toSubmodule ≤ W.toSubmodule → U.toSubmodule ≠ ⊥ → U.toSubmodule = W.toSubmodule) :
    Simple (FDRep.of W.toRepresentation) := by
  rw [rfd_simple_iff]
  change Module.finrank ℂ (Representation.IntertwiningMap W.toRepresentation W.toRepresentation) = 1
  have hnt : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 hW0
  have hid : Representation.IntertwiningMap.id W.toRepresentation ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := exists_ne (0 : W.toSubmodule)
    exact hv (congrArg (fun F : Representation.IntertwiningMap W.toRepresentation
      W.toRepresentation => F v) h0)
  refine (finrank_eq_one_iff_of_nonzero' _ hid).2 fun f => ?_
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f.toLinearMap
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  let K := LinearMap.ker (f.toLinearMap - c • LinearMap.id)
  have hK : ∀ w, w ∈ K ↔ f w = c • w := fun w => by
    simp [K, sub_eq_zero]
  let U : Subrepresentation π :=
    ⟨K.map W.toSubmodule.subtype, by
      rintro g _ ⟨w, hw, rfl⟩
      refine ⟨W.toRepresentation g w, ?_, rfl⟩
      rw [SetLike.mem_coe, hK] at hw
      rw [SetLike.mem_coe, hK, f.isIntertwining, hw, map_smul]⟩
  have hU : U.toSubmodule = W.toSubmodule := by
    refine hW U (Submodule.map_subtype_le _ _) ?_
    rw [Ne, Submodule.eq_bot_iff]
    push Not
    refine ⟨v, ⟨v, (hK v).2 (hv.apply_eq_smul), rfl⟩, ?_⟩
    simpa using hv.2
  refine ⟨c, Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_)⟩
  have hw : (w : X) ∈ U.toSubmodule := by rw [hU]; exact w.2
  obtain ⟨w', hw', hww'⟩ := hw
  rw [Subtype.coe_injective hww'] at hw'
  exact ((hK w).1 hw').symm

/-- A nonzero subrepresentation receives a nonzero intertwining map from a member of any family
representing every simple isomorphism class. -/
theorem rfd_exists_hom_of_ne_bot {ι : Type} (σ : ι → FDRep ℂ G)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i))
    (π : Representation ℂ G X) (P : Subrepresentation π)
    (hP : P.toSubmodule ≠ ⊥) :
    ∃ i, ∃ φ : σ i →ₗ[ℂ] X, φ ≠ 0 ∧ (∀ g, φ ∘ₗ (σ i).ρ g = π g ∘ₗ φ) ∧
      ∀ x, φ x ∈ P.toSubmodule := by
  obtain ⟨W, hWP, hW0, hW⟩ := rfd_exists_minimal π P hP
  obtain ⟨i, ⟨e⟩⟩ := hcov _ (rfd_simple_of_minimal π W hW0 hW)
  have h1 := rfd_finrank_congr e W.toRepresentation
  have h2 : Module.finrank ℂ (Representation.IntertwiningMap (FDRep.of W.toRepresentation).ρ
      W.toRepresentation) = 1 := by
    have := (rfd_simple_iff _).1 (rfd_simple_of_minimal π W hW0 hW)
    exact this
  obtain ⟨α, hα⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (h1 ▸ h2 ▸ Nat.one_pos)
  refine ⟨i, W.toSubmodule.subtype ∘ₗ α.toLinearMap, ?_, fun g => ?_, fun x => hWP (α x).2⟩
  · intro h0
    apply hα
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_)
    have := congrArg (fun F : σ i →ₗ[ℂ] X => F x) h0
    exact Subtype.coe_injective this
  · rw [LinearMap.comp_assoc, α.isIntertwining']
    ext x
    rfl

end Minimal

section Eval

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The action of `G` on `⊕_i σ_i ⊗ M_{σ_i}` through the first factors. -/
def rfd_evalRep {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G) (ρ : Representation ℂ G V) (g : G) :
    Module.End ℂ (∀ i, σ i ⊗[ℂ] rfd_mult (σ i) ρ) :=
  LinearMap.pi fun i => TensorProduct.map ((σ i).ρ g) LinearMap.id ∘ₗ LinearMap.proj i

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem rfd_eval_single {ι : Type} [Fintype ι] [DecidableEq ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (i : ι) (t : σ i ⊗[ℂ] rfd_mult (σ i) ρ) :
    rfd_eval σ ρ (Pi.single i t) =
      TensorProduct.lift ((LinearMap.applyₗ (R := ℂ)).compl₂ (rfd_mult (σ i) ρ).subtype) t := by
  simp only [rfd_eval, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem rfd_eval_single_tmul {ι : Type} [Fintype ι] [DecidableEq ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (i : ι) (x : σ i) (φ : rfd_mult (σ i) ρ) :
    rfd_eval σ ρ (Pi.single i (x ⊗ₜ φ)) = (φ : σ i →ₗ[ℂ] V) x := by
  rw [rfd_eval_single]
  simp

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem rfd_eval_comp_evalRep {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (g : G) :
    rfd_eval σ ρ ∘ₗ rfd_evalRep σ ρ g = ρ g ∘ₗ rfd_eval σ ρ := by
  classical
  refine LinearMap.pi_ext' fun i => TensorProduct.ext' fun x φ => ?_
  simp only [LinearMap.comp_apply, rfd_eval, rfd_evalRep, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j = i
  · subst h
    simp
    exact LinearMap.congr_fun (φ.2 g) x
  · simp [h]

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem rfd_eval_comp_evalAct {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (u : Module.End ℂ V)
    (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) :
    rfd_eval σ ρ ∘ₗ rfd_evalAct σ ρ u hu = u ∘ₗ rfd_eval σ ρ := by
  classical
  refine LinearMap.pi_ext' fun i => TensorProduct.ext' fun x φ => ?_
  simp only [LinearMap.comp_apply, rfd_eval, rfd_evalAct, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j = i
  · subst h; simp; rfl
  · simp [h]

theorem rfd_eval_surjective {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i)) :
    Function.Surjective (rfd_eval σ ρ) := by
  classical
  let R : Subrepresentation ρ :=
    ⟨LinearMap.range (rfd_eval σ ρ), by
      rintro g _ ⟨s, rfl⟩
      exact ⟨rfd_evalRep σ ρ g s, LinearMap.congr_fun (rfd_eval_comp_evalRep σ ρ g) s⟩⟩
  rw [← LinearMap.range_eq_top]
  by_contra hR
  obtain ⟨C, hC⟩ := rfd_exists_compl ρ R
  have hC0 : C.toSubmodule ≠ ⊥ := by
    intro h0
    rw [h0] at hC
    exact hR (eq_top_of_isCompl_bot hC)
  obtain ⟨i, φ, hφ0, hφ, hφC⟩ := rfd_exists_hom_of_ne_bot σ hcov ρ C hC0
  apply hφ0
  ext x
  have hR' : φ x ∈ R.toSubmodule :=
    ⟨Pi.single i (x ⊗ₜ ⟨φ, hφ⟩), rfd_eval_single_tmul σ ρ i x ⟨φ, hφ⟩⟩
  have := hC.disjoint.le_bot ⟨hR', hφC x⟩
  simpa using this

omit [FiniteDimensional ℂ V] in
/-- The action of `G` on families `(x_{i,k})` with `x_{i,k} ∈ σ_i`. -/
def rfd_coordRep {ι : Type} (σ : ι → FDRep ℂ G) (m : ι → ℕ) :
    Representation ℂ G (∀ i, Fin (m i) → σ i) where
  toFun g := LinearMap.pi fun i => LinearMap.pi fun k =>
    (σ i).ρ g ∘ₗ LinearMap.proj k ∘ₗ LinearMap.proj i
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

omit [Fintype G] [FiniteDimensional ℂ V] in
theorem rfd_coordRep_apply {ι : Type} (σ : ι → FDRep ℂ G) (m : ι → ℕ) (g : G)
    (x : ∀ i, Fin (m i) → σ i) (i : ι) (k : Fin (m i)) :
    rfd_coordRep σ m g x i k = (σ i).ρ g (x i k) := rfl

/-- The dimension of `⊕_i σ_i ⊗ M_{σ_i}` is at most `dim V`: choosing bases of the multiplicity
spaces, the map `(x_{i,k}) ↦ Σ φ_{i,k}(x_{i,k})` is injective. -/
theorem rfd_finrank_source_le {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i)) :
    Module.finrank ℂ (∀ i, σ i ⊗[ℂ] rfd_mult (σ i) ρ) ≤ Module.finrank ℂ V := by
  classical
  let m : ι → ℕ := fun i => Module.finrank ℂ (rfd_mult (σ i) ρ)
  let b : ∀ i, Module.Basis (Fin (m i)) ℂ (rfd_mult (σ i) ρ) := fun i => Module.finBasis ℂ _
  let Φ : (∀ i, Fin (m i) → σ i) →ₗ[ℂ] V :=
    ∑ i, ∑ k, ((b i k : rfd_mult (σ i) ρ) : σ i →ₗ[ℂ] V) ∘ₗ LinearMap.proj k ∘ₗ LinearMap.proj i
  have hΦ : ∀ x, Φ x = ∑ i, ∑ k, ((b i k : rfd_mult (σ i) ρ) : σ i →ₗ[ℂ] V) (x i k) := fun x => by
    simp [Φ]
  have hΦG : ∀ g x, Φ (rfd_coordRep σ m g x) = ρ g (Φ x) := fun g x => by
    rw [hΦ, hΦ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rfd_coordRep_apply]
    exact LinearMap.congr_fun ((b i k).2 g) (x i k)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hK0
    let K : Subrepresentation (rfd_coordRep σ m) :=
      ⟨LinearMap.ker Φ, fun g x hx => by
        rw [LinearMap.mem_ker] at hx ⊢
        rw [hΦG, hx, map_zero]⟩
    obtain ⟨j, α, hα0, hα, hαK⟩ := rfd_exists_hom_of_ne_bot σ hcov _ K hK0
    have hcomp : ∀ i k g y, α ((σ j).ρ g y) i k = (σ i).ρ g (α y i k) := fun i k g y => by
      have := LinearMap.congr_fun (hα g) y
      simp only [LinearMap.comp_apply] at this
      rw [this, rfd_coordRep_apply]
    let L : ∀ i, Fin (m i) → Representation.IntertwiningMap (σ j).ρ (σ i).ρ := fun i k =>
      { toLinearMap := LinearMap.proj k ∘ₗ LinearMap.proj i ∘ₗ α
        isIntertwining' := fun g => LinearMap.ext fun y => hcomp i k g y }
    have hLapp : ∀ i k y, L i k y = α y i k := fun _ _ _ => rfl
    have hzero : ∀ i, i ≠ j → ∀ k y, α y i k = 0 := fun i hij k y => by
      have := hσ i
      have := hσ j
      have h := rfd_intertwining_eq_zero (σ j) (σ i) (fun ⟨e⟩ => hij (hdist i j ⟨e⟩)) (L i k)
      rw [← hLapp, h]
      rfl
    have hsc : ∀ k, ∃ c : ℂ, ∀ y, α y j k = c • y := fun k => by
      have := hσ j
      obtain ⟨c, hc⟩ := rfd_intertwining_eq_smul (σ j) (L j k)
      exact ⟨c, fun y => by rw [← hLapp, hc]; rfl⟩
    choose c hc using hsc
    have hsum : (∑ k, c k • b j k) = 0 := by
      apply Subtype.ext
      refine LinearMap.ext fun y => ?_
      have h0 : Φ (α y) = 0 := hαK y
      rw [hΦ, Finset.sum_eq_single j] at h0
      · simpa [hc] using h0
      · intro i _ hij
        exact Finset.sum_eq_zero fun k _ => by rw [hzero i hij k y, map_zero]
      · simp
    have hc0 := Fintype.linearIndependent_iff.1 (b j).linearIndependent c hsum
    apply hα0
    refine LinearMap.ext fun y => funext fun i => funext fun k => ?_
    by_cases hij : i = j
    · subst hij
      rw [hc, hc0, zero_smul]
      rfl
    · rw [hzero i hij k y]
      rfl
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank ℂ (∀ i, Fin (m i) → σ i) =
      Module.finrank ℂ (∀ i, σ i ⊗[ℂ] rfd_mult (σ i) ρ) := by
    simp only [Module.finrank_pi_fintype, Module.finrank_tensorProduct, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, m]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  omega

theorem rfd_eval_bijective' {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i)) :
    Function.Bijective (rfd_eval σ ρ) := by
  have hs := rfd_eval_surjective σ ρ hcov
  have hle := rfd_finrank_source_le σ ρ hσ hdist hcov
  have hge : Module.finrank ℂ V ≤ Module.finrank ℂ (∀ i, σ i ⊗[ℂ] rfd_mult (σ i) ρ) := by
    have := LinearMap.finrank_range_le (rfd_eval σ ρ)
    rwa [LinearMap.range_eq_top.2 hs, finrank_top] at this
  refine ⟨?_, hs⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm hle hge)).2 hs

end Eval

end HodgeLean.Foundations
