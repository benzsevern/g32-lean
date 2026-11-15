import HodgeLean.Foundations.Program.HurwitzPrymRexConj
import HodgeLean.Foundations.Program.HurwitzPrymDefs
import HodgeLean.Foundations.Program.HurwitzPrymCovGalois

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rex`: the conjugate representation and Chevalley–Weil on `H₁`

The complex conjugate `ρ̄` of a representation (the same group action on `V` with conjugated
scalars) is irreducible with `ρ`, has the same dimension, and its multiplicity in `F` is the
multiplicity of `ρ` in `F̄`. For `M` of finite order, `age M + age M̄ = rk (M - 1)`.
With `b4_homG_split` and `b4_hodge_eq_holo` this reduces the topological Chevalley–Weil count
to the holomorphic one for `ρ` and `ρ̄`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open scoped TensorProduct ComplexConjugate
open HodgeLean.Papers

namespace HodgeLean.Foundations.Program

/-! ## The conjugate space -/

/-- **The complex conjugate** `V̄` of a complex vector space: `V` with `c • v := c̄ v`.
Source: Fulton–Harris, *Representation Theory*, GTM 129, §3.5 (complex conjugate
representations). -/
structure HurwitzPrymRex_Bar (V : Type) where
  of ::
  val : V

namespace HurwitzPrymRex_Bar

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem val_injective : Function.Injective (val : HurwitzPrymRex_Bar V → V) := by
  rintro ⟨a⟩ ⟨b⟩ h
  cases h
  rfl

@[ext] theorem ext {x y : HurwitzPrymRex_Bar V} (h : x.val = y.val) : x = y := val_injective h

/-- The identification `V̄ ≃ V` of sets.
Source: Fulton–Harris, *Representation Theory*, GTM 129, §3.5. -/
def equiv : HurwitzPrymRex_Bar V ≃ V where
  toFun := val
  invFun := of
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (HurwitzPrymRex_Bar V) := equiv.addCommGroup

@[simp] theorem val_add (x y : HurwitzPrymRex_Bar V) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_zero : (0 : HurwitzPrymRex_Bar V).val = 0 := rfl
@[simp] theorem val_neg (x : HurwitzPrymRex_Bar V) : (-x).val = -x.val := rfl
@[simp] theorem val_sub (x y : HurwitzPrymRex_Bar V) : (x - y).val = x.val - y.val := rfl

instance : Module ℂ (HurwitzPrymRex_Bar V) where
  smul c x := of (conj c • x.val)
  one_smul x := ext (by change conj (1 : ℂ) • x.val = x.val; simp)
  mul_smul a b x := ext (by change conj (a * b) • x.val = conj a • conj b • x.val; simp [mul_smul])
  smul_zero a := ext (by change conj a • (0 : V) = 0; simp)
  smul_add a x y := ext (by change conj a • (x.val + y.val) = conj a • x.val + conj a • y.val
                            simp [smul_add])
  add_smul a b x := ext (by change conj (a + b) • x.val = conj a • x.val + conj b • x.val
                            simp [add_smul])
  zero_smul x := ext (by change conj (0 : ℂ) • x.val = 0; simp)

@[simp] theorem val_smul (c : ℂ) (x : HurwitzPrymRex_Bar V) : (c • x).val = conj c • x.val := rfl

example (x : HurwitzPrymRex_Bar V) : ((1 : ℂ) • x) = x := one_smul ℂ x

/-- `val` as a conjugate-linear additive equivalence.
Source: Fulton–Harris, *Representation Theory*, GTM 129, §3.5. -/
def addEquiv : HurwitzPrymRex_Bar V ≃+ V where
  toEquiv := equiv
  map_add' _ _ := rfl

example (x : HurwitzPrymRex_Bar V) : addEquiv x = x.val := rfl

theorem rank_eq : Module.rank ℂ (HurwitzPrymRex_Bar V) = Module.rank ℂ V :=
  rank_eq_of_equiv_equiv (fun c : ℂ ↦ conj c) addEquiv
    (Function.Involutive.bijective (f := fun c : ℂ ↦ conj c) Complex.conj_conj)
    (fun _ _ ↦ rfl)

theorem finrank_eq : Module.finrank ℂ (HurwitzPrymRex_Bar V) = Module.finrank ℂ V := by
  simp only [Module.finrank, rank_eq]

instance [FiniteDimensional ℂ V] : FiniteDimensional ℂ (HurwitzPrymRex_Bar V) :=
  Module.finite_of_rank_eq_nat (n := Module.finrank ℂ V) (by rw [rank_eq, Module.finrank_eq_rank])

end HurwitzPrymRex_Bar

open HurwitzPrymRex_Bar

/-! ## The conjugate representation -/

section Rep

variable {G : Type} [Group G]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- **The conjugate representation** `ρ̄` on `V̄`.
Source: Fulton–Harris, GTM 129, §3.5. -/
def HurwitzPrymRex_barRep (ρ : Representation ℂ G V) : Representation ℂ G (HurwitzPrymRex_Bar V) where
  toFun g :=
    { toFun := fun x ↦ of (ρ g x.val)
      map_add' := fun x y ↦ ext (by simp)
      map_smul' := fun c x ↦ ext (by simp) }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp] theorem HurwitzPrymRex_barRep_val (ρ : Representation ℂ G V) (g : G)
    (x : HurwitzPrymRex_Bar V) : (HurwitzPrymRex_barRep ρ g x).val = ρ g x.val := rfl

example (ρ : Representation ℂ G V) (x : HurwitzPrymRex_Bar V) : HurwitzPrymRex_barRep ρ 1 x = x := by
  simp

/-- Subrepresentations of `ρ` and of `ρ̄` have the same underlying sets.
Source: Fulton–Harris, *Representation Theory*, GTM 129, §3.5 (`ρ̄` is irreducible with `ρ`). -/
def HurwitzPrymRex_subrepIso (ρ : Representation ℂ G V) :
    Subrepresentation ρ ≃o Subrepresentation (HurwitzPrymRex_barRep ρ) where
  toFun W :=
    { toSubmodule :=
        { carrier := {x | x.val ∈ W.toSubmodule}
          add_mem' := fun hx hy ↦ by simpa using W.toSubmodule.add_mem hx hy
          zero_mem' := by simp
          smul_mem' := fun c x hx ↦ by simpa using W.toSubmodule.smul_mem (conj c) hx }
      apply_mem_toSubmodule := fun g x hx ↦ by
        change ρ g x.val ∈ W.toSubmodule
        exact W.apply_mem_toSubmodule g hx }
  invFun W :=
    { toSubmodule :=
        { carrier := {v | of v ∈ W.toSubmodule}
          add_mem' := fun {v w} hv hw ↦ by
            have := W.toSubmodule.add_mem hv hw
            exact this
          zero_mem' := W.toSubmodule.zero_mem
          smul_mem' := fun c v hv ↦ by
            have := W.toSubmodule.smul_mem (conj c) hv
            change of (c • v) ∈ W.toSubmodule
            convert this using 1
            ext
            simp }
      apply_mem_toSubmodule := fun g v hv ↦ W.apply_mem_toSubmodule g hv }
  left_inv W := by
    apply Subrepresentation.toSubmodule_injective
    ext v
    rfl
  right_inv W := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    rfl
  map_rel_iff' {W W'} := by
    change (∀ x : HurwitzPrymRex_Bar V, x.val ∈ W.toSubmodule → x.val ∈ W'.toSubmodule) ↔
      ∀ v, v ∈ W.toSubmodule → v ∈ W'.toSubmodule
    exact ⟨fun h v hv ↦ h (of v) hv, fun h x hx ↦ h _ hx⟩

example (ρ : Representation ℂ G V) (W : Subrepresentation ρ) (v : V) :
    v ∈ W.toSubmodule ↔ HurwitzPrymRex_Bar.of v ∈ (HurwitzPrymRex_subrepIso ρ W).toSubmodule :=
  Iff.rfl

instance HurwitzPrymRex_barRep_isIrreducible (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    (HurwitzPrymRex_barRep ρ).IsIrreducible :=
  (HurwitzPrymRex_subrepIso ρ).symm.isSimpleOrder

theorem HurwitzPrymRex_barRep_nontrivial (ρ : Representation ℂ G V)
    (hρ : ∃ (g : G) (v : V), ρ g v ≠ v) :
    ∃ (g : G) (v : HurwitzPrymRex_Bar V), HurwitzPrymRex_barRep ρ g v ≠ v := by
  obtain ⟨g, v, h⟩ := hρ
  exact ⟨g, of v, fun h' ↦ h (congrArg val h')⟩

end Rep

/-! ## Multiplicities in `F̄` -/

section Hom

variable {G : Type} [Group G]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {Λ : Type*} [AddCommGroup Λ]

/-- **`m_ρ(F̄) = m_ρ̄(F)`**: conjugation `φ ↦ conj ∘ φ` identifies the `G`-maps. -/
theorem HurwitzPrymRex_finrank_homG_bar (f : G → (Λ →+ Λ)) (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    (ρ : Representation ℂ G V) :
    Module.finrank ℂ (b4_HomG ρ (fun g ↦ b2_cplxMap (f g)) (b2_conjSubmodule Λ F)) =
      Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep ρ) (fun g ↦ b2_cplxMap (f g)) F) := by
  let fwd : b4_HomG ρ (fun g ↦ b2_cplxMap (f g)) (b2_conjSubmodule Λ F) →
      b4_HomG (HurwitzPrymRex_barRep ρ) (fun g ↦ b2_cplxMap (f g)) F := fun φ ↦
    ⟨{ toFun := fun x ↦ b2_conj Λ (φ.1 x.val)
       map_add' := fun x y ↦ by simp
       map_smul' := fun c x ↦ by
         simp only [val_smul, map_smul, b4cov_conj_smul, Complex.conj_conj, RingHom.id_apply] },
      fun x ↦ b2a_conj_mem_of_mem_conjSubmodule (φ.2.1 x.val),
      fun g x ↦ by
        change b2_conj Λ (φ.1 (ρ g x.val)) = b2_cplxMap (f g) (b2_conj Λ (φ.1 x.val))
        rw [φ.2.2 g x.val, HurwitzPrymRex_cplxMap_conj]⟩
  let bwd : b4_HomG (HurwitzPrymRex_barRep ρ) (fun g ↦ b2_cplxMap (f g)) F →
      b4_HomG ρ (fun g ↦ b2_cplxMap (f g)) (b2_conjSubmodule Λ F) := fun ψ ↦
    ⟨{ toFun := fun v ↦ b2_conj Λ (ψ.1 (of v))
       map_add' := fun v w ↦ by
         rw [show of (v + w) = of v + of w from rfl, map_add, map_add]
       map_smul' := fun c v ↦ by
         rw [show of (c • v) = conj c • of v from ext (by simp), map_smul, b4cov_conj_smul,
           Complex.conj_conj, RingHom.id_apply] },
      fun v ↦ b2a_conj_mem_conjSubmodule (ψ.2.1 (of v)),
      fun g v ↦ by
        change b2_conj Λ (ψ.1 (HurwitzPrymRex_barRep ρ g (of v))) =
          b2_cplxMap (f g) (b2_conj Λ (ψ.1 (of v)))
        rw [ψ.2.2 g (of v), HurwitzPrymRex_cplxMap_conj]⟩
  let j : b4_HomG ρ (fun g ↦ b2_cplxMap (f g)) (b2_conjSubmodule Λ F) ≃+
      b4_HomG (HurwitzPrymRex_barRep ρ) (fun g ↦ b2_cplxMap (f g)) F :=
    { toFun := fwd
      invFun := bwd
      left_inv := fun φ ↦ by
        apply Subtype.ext
        ext v
        exact b4cov_conj_conj _
      right_inv := fun ψ ↦ by
        apply Subtype.ext
        ext x
        exact b4cov_conj_conj _
      map_add' := fun φ ψ ↦ by
        apply Subtype.ext
        ext x
        change b2_conj Λ (φ.1 x.val + ψ.1 x.val) = _
        rw [map_add]
        rfl }
  have hr := rank_eq_of_equiv_equiv (fun c : ℂ ↦ conj c) j
    (Function.Involutive.bijective (f := fun c : ℂ ↦ conj c) Complex.conj_conj)
    (fun c φ ↦ by
      apply Subtype.ext
      ext x
      change b2_conj Λ (c • φ.1 x.val) = conj c • b2_conj Λ (φ.1 x.val)
      rw [b4cov_conj_smul])
  simp only [Module.finrank, hr]

end Hom

/-! ## Ages of conjugate maps -/

section Age

open Polynomial Module.End

variable {G : Type} [Group G] [Finite G]
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem HurwitzPrymRex_isSemisimple {T : V →ₗ[ℂ] V} {m : ℕ} (hm : m ≠ 0) (hT : T ^ m = 1) :
    Module.End.IsSemisimple T := by
  apply isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ m - C 1)
  · exact (separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hm) one_ne_zero).squarefree
  · simp [hT]

theorem HurwitzPrymRex_count_roots {T : V →ₗ[ℂ] V} (hT : Module.End.IsSemisimple T) (μ : ℂ) :
    T.charpoly.roots.count μ = Module.finrank ℂ (eigenspace T μ) := by
  classical
  rw [count_roots, ← LinearMap.finrank_maxGenEigenspace_eq,
    hT.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]

theorem HurwitzPrymRex_rep_pow (ρ : Representation ℂ G V) (g : G) :
    ρ g ^ Nat.card G = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

theorem HurwitzPrymRex_finrank_eigenspace_bar (ρ : Representation ℂ G V) (g : G) (μ : ℂ) :
    Module.finrank ℂ (eigenspace (HurwitzPrymRex_barRep ρ g) μ) =
      Module.finrank ℂ (eigenspace (ρ g) (conj μ)) := by
  let j : eigenspace (HurwitzPrymRex_barRep ρ g) μ ≃+ eigenspace (ρ g) (conj μ) :=
    { toFun := fun x ↦ ⟨x.1.val, by
        have := mem_eigenspace_iff.1 x.2
        rw [mem_eigenspace_iff]
        exact congrArg val this⟩
      invFun := fun v ↦ ⟨of v.1, by
        have := mem_eigenspace_iff.1 v.2
        rw [mem_eigenspace_iff]
        ext
        simpa using this⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  have hr := rank_eq_of_equiv_equiv (fun c : ℂ ↦ conj c) j
    (Function.Involutive.bijective (f := fun c : ℂ ↦ conj c) Complex.conj_conj)
    (fun _ _ ↦ rfl)
  simp only [Module.finrank, hr]

theorem HurwitzPrymRex_roots_bar (ρ : Representation ℂ G V) (g : G) :
    (HurwitzPrymRex_barRep ρ g).charpoly.roots = (ρ g).charpoly.roots.map (starRingEnd ℂ) := by
  classical
  have hm : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hs := HurwitzPrymRex_isSemisimple hm (HurwitzPrymRex_rep_pow ρ g)
  have hs' := HurwitzPrymRex_isSemisimple hm (HurwitzPrymRex_rep_pow (HurwitzPrymRex_barRep ρ) g)
  ext μ
  rw [HurwitzPrymRex_count_roots hs', HurwitzPrymRex_finrank_eigenspace_bar,
    ← HurwitzPrymRex_count_roots hs]
  conv_rhs => rw [show μ = starRingEnd ℂ (conj μ) from (Complex.conj_conj μ).symm]
  rw [Multiset.count_map_eq_count' _ _ (RingHom.injective _)]

theorem HurwitzPrymRex_toIcoMod_self {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * Real.pi) :
    toIcoMod Real.two_pi_pos 0 x = x :=
  (toIcoMod_eq_self _).2 ⟨h0, by rwa [zero_add]⟩

/-- **`angle λ + angle λ̄ = [λ ≠ 1]`** for a root of unity `λ`. -/
theorem HurwitzPrymRex_angle_add_conj {l : ℂ} {m : ℕ} (hm : m ≠ 0) (h : l ^ m = 1) :
    g32h_angle (conj l) + g32h_angle l = if l = 1 then 0 else 1 := by
  have hpi := Real.pi_pos
  split_ifs with h1
  · subst h1
    simp [g32h_angle]
  have hn : ‖l‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h hm
  have harg0 : Complex.arg l ≠ 0 := by
    intro h0
    apply h1
    have := Complex.norm_mul_exp_arg_mul_I l
    rw [hn, h0] at this
    simpa using this.symm
  have hlo := Complex.neg_pi_lt_arg l
  have hhi := Complex.arg_le_pi l
  simp only [g32h_angle]
  rw [← add_div, div_eq_one_iff_eq (by positivity)]
  by_cases hpi' : Complex.arg l = Real.pi
  · rw [Complex.arg_conj, if_pos hpi', hpi', HurwitzPrymRex_toIcoMod_self hpi.le (by linarith)]
    ring
  rw [Complex.arg_conj, if_neg hpi']
  rcases lt_or_gt_of_ne harg0 with hneg | hpos
  · rw [HurwitzPrymRex_toIcoMod_self (by linarith) (by linarith),
      ← toIcoMod_add_right Real.two_pi_pos 0 (Complex.arg l),
      HurwitzPrymRex_toIcoMod_self (by linarith) (by linarith)]
    ring
  · rw [← toIcoMod_add_right Real.two_pi_pos 0 (-Complex.arg l),
      HurwitzPrymRex_toIcoMod_self (by linarith) (by linarith),
      HurwitzPrymRex_toIcoMod_self (by linarith) (by linarith)]
    ring

theorem HurwitzPrymRex_sum_ite_one (s : Multiset ℂ) :
    (s.map fun l ↦ if l = 1 then (0 : ℝ) else 1).sum = s.card - s.count 1 := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.card_cons, Multiset.count_cons]
    by_cases ha : a = 1
    · subst ha
      rw [if_pos rfl, if_pos rfl]
      push_cast
      ring
    · rw [if_neg ha, if_neg fun h ↦ ha h.symm]
      push_cast
      ring

theorem HurwitzPrymRex_root_pow (ρ : Representation ℂ G V) (g : G) {l : ℂ}
    (hl : l ∈ (ρ g).charpoly.roots) : l ^ Nat.card G = 1 := by
  have hroot := (mem_roots (LinearMap.charpoly_monic _).ne_zero).1 hl
  obtain ⟨v, hv⟩ := ((hasEigenvalue_iff_isRoot_charpoly _ _).2 hroot).exists_hasEigenvector
  have hpow : ∀ k : ℕ, (ρ g ^ k) v = l ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, hv.apply_eq_smul, map_smul, ih, smul_smul, pow_succ,
        mul_comm]
  have h := hpow (Nat.card G)
  rw [HurwitzPrymRex_rep_pow, Module.End.one_apply] at h
  have h' : (l ^ Nat.card G - 1) • v = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_right hv.2)

/-- **`age ρ̄(g) + age ρ(g) = rk (ρ(g) - 1)`**. -/
theorem HurwitzPrymRex_age_add_bar (ρ : Representation ℂ G V) (g : G) :
    b4_age (HurwitzPrymRex_barRep ρ g) + b4_age (ρ g) =
      Module.finrank ℂ (LinearMap.range (ρ g - LinearMap.id)) := by
  classical
  have hm : Nat.card G ≠ 0 := Nat.card_pos.ne'
  simp only [b4_age]
  rw [HurwitzPrymRex_roots_bar, Multiset.map_map, ← Multiset.sum_map_add]
  simp only [Function.comp_apply]
  rw [Multiset.map_congr rfl (fun l hl ↦ HurwitzPrymRex_angle_add_conj hm
      (HurwitzPrymRex_root_pow ρ g hl)), HurwitzPrymRex_sum_ite_one,
    IsAlgClosed.card_roots_eq_natDegree, LinearMap.charpoly_natDegree,
    HurwitzPrymRex_count_roots (HurwitzPrymRex_isSemisimple hm (HurwitzPrymRex_rep_pow ρ g))]
  have hker : eigenspace (ρ g) 1 = LinearMap.ker (ρ g - LinearMap.id) := by
    ext v
    rw [mem_eigenspace_iff, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      one_smul, sub_eq_zero]
  rw [hker]
  have := LinearMap.finrank_range_add_finrank_ker (ρ g - LinearMap.id)
  rw [← this]
  push_cast
  ring

theorem HurwitzPrymRex_age_nonneg {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : W →ₗ[ℂ] W) : 0 ≤ b4_age T := by
  simp only [b4_age]
  refine Multiset.sum_nonneg fun a ha ↦ ?_
  obtain ⟨l, -, rfl⟩ := Multiset.mem_map.1 ha
  simp only [g32h_angle]
  exact div_nonneg (toIcoMod_mem_Ico Real.two_pi_pos 0 _).1 Real.two_pi_pos.le

theorem HurwitzPrymRex_age_one (ρ : Representation ℂ G V) :
    b4_age (ρ 1) = 0 ∧ b4_age (HurwitzPrymRex_barRep ρ 1) = 0 := by
  have h := HurwitzPrymRex_age_add_bar ρ 1
  have hz : ρ 1 - LinearMap.id = 0 := by rw [map_one]; exact sub_self _
  rw [hz, LinearMap.range_zero, finrank_bot, Nat.cast_zero] at h
  have h1 := HurwitzPrymRex_age_nonneg (HurwitzPrymRex_barRep ρ 1)
  have h2 := HurwitzPrymRex_age_nonneg (ρ 1)
  constructor <;> linarith

end Age

/-! ## Points with a nontrivial stabilizer -/

section Fixed

open Manifold Topology
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {G : Type} [Group G] [MulAction G C]

/-- **Finitely many points have a nontrivial stabilizer** on a compact surface. -/
theorem HurwitzPrymRex_fixedPoints_finite [Finite G] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [FaithfulSMul G C] (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) :
    {x : C | ∃ k : G, k ≠ 1 ∧ k • x = x}.Finite := by
  have : {x : C | ∃ k : G, k ≠ 1 ∧ k • x = x} = ⋃ k : {k : G // k ≠ 1}, {x | k.1 • x = x} := by
    ext x
    simp
  rw [this]
  refine Set.finite_iUnion fun k ↦ ?_
  have hcl : IsClosed {x : C | k.1 • x = x} :=
    isClosed_eq (hG k.1).continuous continuous_id
  refine hcl.isCompact.finite ?_
  rw [isDiscrete_iff_discreteTopology, discreteTopology_subtype_iff]
  intro x hx
  have hiso := b4cov_fixed_isolated hE hG x k.1 hx k.2
  rw [Filter.inf_principal_eq_bot]
  exact Filter.mem_inf_of_inter hiso (Filter.mem_principal_self {x}ᶜ) fun z ⟨hz, hzx⟩ hfix ↦
    hzx (hz hfix)

end Fixed

end HodgeLean.Foundations.Program
