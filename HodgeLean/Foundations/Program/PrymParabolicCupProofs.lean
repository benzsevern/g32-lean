import HodgeLean.Foundations.Program.PrymParabolicCupDefs

/-! # Proofs for stage H4, algebraic part: the cup form on `H¹_σ` and the passage to `K`

The `_aux` theorems that `PrymParabolicCup.lean` restates.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Matrix

namespace HodgeLean.Foundations.Program

theorem hg4_cup_coboundary_left_aux {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]
    [StarRing K] {ι : Type*} [Fintype ι] {r : ℕ} (g : Fin r → G) (H : Matrix ι ι K)
    (φ : hg_Vert g → ι → K) (β : hg_Edge G r → ι → K)
    (hβ : β ∈ LinearMap.ker (hg_delta1 K (ι → K) g)) :
    hg4_cupForm g H (hg_delta0 K (ι → K) g φ) β = 0 := by
  let c : hg_Edge G r → K := fun ε => star (φ (hg_src g ε)) ⬝ᵥ (H *ᵥ β ε)
  have hb : ∀ τ, β (hg_face0 g τ) - β (hg_face1 τ) + β (hg_face2 τ) = 0 :=
    fun τ => congrFun (LinearMap.mem_ker.mp hβ) τ
  have he : hg_cup g H (hg_delta0 K (ι → K) g φ) β = hg_delta1 K K g c := by
    funext τ
    have hs : hg_src g (hg_face0 g τ) = hg_tgt g (hg_face2 τ) := by
      rcases τ with ⟨i, x⟩ | ⟨i, x⟩
      · rfl
      · have hc : ((x * (g i)⁻¹ : G) : G ⧸ Subgroup.zpowers (g i)) = (x : G ⧸ _) := by
          rw [QuotientGroup.eq]
          simp
        simp only [hg_face0, hg_src, hg_face2, hg_tgt, hc]
    have hs' : hg_src g (hg_face1 τ) = hg_src g (hg_face2 τ) := by
      rcases τ with ⟨i, x⟩ | ⟨i, x⟩ <;> rfl
    have hb' := congrArg (fun v => star (φ (hg_src g (hg_face2 τ))) ⬝ᵥ (H *ᵥ v)) (hb τ)
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_zero, dotProduct_add,
      dotProduct_sub, dotProduct_zero] at hb'
    change star (φ (hg_tgt g (hg_face2 τ)) - φ (hg_src g (hg_face2 τ))) ⬝ᵥ
      (H *ᵥ β (hg_face0 g τ)) = _
    rw [hg_delta1_eq]
    dsimp only [c]
    rw [hs, hs']
    simp only [star_sub, sub_dotProduct]
    linear_combination -hb'
  change hg_fundEval (hg_cup g H (hg_delta0 K (ι → K) g φ) β) = 0
  rw [he]
  exact hg_fundEval_delta1 g c

theorem hg4_cup_coboundary_right_aux {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]
    [StarRing K] {ι : Type*} [Fintype ι] {r : ℕ} (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (H : Matrix ι ι K) (α : hg_Edge G r → ι → K)
    (hα : α ∈ LinearMap.ker (hg_delta1 K (ι → K) g)) (φ : hg_Vert g → ι → K) :
    hg4_cupForm g H α (hg_delta0 K (ι → K) g φ) = 0 := by
  let c : hg_Edge G r → K := fun ε => star (α ε) ⬝ᵥ (H *ᵥ φ (hg_tgt g ε))
  have ha : ∀ τ, α (hg_face0 g τ) - α (hg_face1 τ) + α (hg_face2 τ) = 0 :=
    fun τ => congrFun (LinearMap.mem_ker.mp hα) τ
  have he : hg_cup g H α (hg_delta0 K (ι → K) g φ) = -hg_delta1 K K g c := by
    funext τ
    have hs : hg_src g (hg_face0 g τ) = hg_tgt g (hg_face2 τ) := by
      rcases τ with ⟨i, x⟩ | ⟨i, x⟩
      · rfl
      · have hc : ((x * (g i)⁻¹ : G) : G ⧸ Subgroup.zpowers (g i)) = (x : G ⧸ _) := by
          rw [QuotientGroup.eq]
          simp
        simp only [hg_face0, hg_src, hg_face2, hg_tgt, hc]
    have ht : hg_tgt g (hg_face0 g τ) = hg_tgt g (hg_face1 τ) := by
      rcases τ with ⟨i, x⟩ | ⟨i, x⟩
      · rfl
      · simp only [hg_face0, hg_face1, hg_tgt, hg_Q_rotate g hprod,
          _root_.mul_inv_rev, mul_assoc]
    have ha' := congrArg (fun v => star v ⬝ᵥ (H *ᵥ φ (hg_tgt g (hg_face1 τ)))) (ha τ)
    simp only [star_add, star_sub, star_zero, add_dotProduct, sub_dotProduct,
      zero_dotProduct] at ha'
    change star (α (hg_face2 τ)) ⬝ᵥ
      (H *ᵥ (φ (hg_tgt g (hg_face0 g τ)) - φ (hg_src g (hg_face0 g τ)))) = _
    change _ = -(hg_delta1 K K g c τ)
    rw [hg_delta1_eq]
    dsimp only [c]
    rw [hs, ht]
    simp only [Matrix.mulVec_sub, dotProduct_sub]
    linear_combination ha'
  change hg_fundEval (hg_cup g H α (hg_delta0 K (ι → K) g φ)) = 0
  rw [he]
  have hn : hg_fundEval (-hg_delta1 K K g c) = -hg_fundEval (hg_delta1 K K g c) := by
    unfold hg_fundEval
    simp only [Pi.neg_apply]
    simp_rw [show ∀ a b : K, -a - -b = -(a - b) by intros; abel]
    simp only [Finset.sum_neg_distrib]
  rw [hn, hg_fundEval_delta1 g c, neg_zero]

theorem hg4_cupH1_mk_aux {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K] [StarRing K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) (H : Matrix ι ι K) (α β : hg_eqCocycles σ g) :
    hg4_cupH1 σ g H (Submodule.Quotient.mk α) (Submodule.Quotient.mk β) =
      hg4_cupForm g H α β := by
  have hlift : ∀ a : hg_eqCocycles σ g,
      (hg4_lift σ g (Submodule.Quotient.mk a) : hg_Edge G r → ι → K) - a ∈
        hg_eqCoboundaries σ g := fun a => by
    have h : Submodule.Quotient.mk (hg4_lift σ g (Submodule.Quotient.mk a)) =
        (Submodule.Quotient.mk a : hg_eqH1 σ g) :=
      Submodule.mk_quotientEquivOfIsCompl_apply
        (Classical.choose_spec (Submodule.exists_isCompl _)) _
    rw [Submodule.Quotient.eq, Submodule.mem_comap] at h
    change ((hg4_lift σ g (Submodule.Quotient.mk a) : hg_Edge G r → ι → K) - a) ∈
      hg_eqCoboundaries σ g at h
    exact h
  obtain ⟨φ, hφ, heφ⟩ := hlift α
  obtain ⟨ψ, hψ, heψ⟩ := hlift β
  have hleft := hg4_cup_coboundary_left_aux g H φ
    (hg4_lift σ g (Submodule.Quotient.mk β)) (hg4_lift σ g _).2.2
  have hright := hg4_cup_coboundary_right_aux g hprod H α α.2.2 ψ
  rw [heφ, map_sub, LinearMap.sub_apply] at hleft
  rw [heψ, map_sub] at hright
  change hg4_cupForm g H (hg4_lift σ g (Submodule.Quotient.mk α))
    (hg4_lift σ g (Submodule.Quotient.mk β)) = hg4_cupForm g H α β
  linear_combination hleft + hright

theorem hg4_shapiroH1_bijective_aux {G : Type*} [Group G] {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K) (g : Fin r → G)
    (hprod : (List.ofFn g).prod = 1) :
    Function.Bijective (hg4_shapiroH1 σ g) := by
  constructor
  · intro x y h
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Submodule.Quotient.mk (hg4_shapiroZ σ g a) =
      (Submodule.Quotient.mk (hg4_shapiroZ σ g b) : hg_eqH1 σ g) at h
    apply (Submodule.Quotient.eq _).mpr
    have hc := (Submodule.Quotient.eq _).mp h
    change hg_shapiroCochain σ g a - hg_shapiroCochain σ g b ∈ hg_eqCoboundaries σ g at hc
    have hc' : hg_shapiroCochain σ g (a - b) ∈ hg_eqCoboundaries σ g := by
      simpa only [map_sub] using hc
    exact (hg_shapiro_coboundary_iff σ g _).mp hc'
  · intro x
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a, ha, hc⟩ := hg_shapiro_surjective σ g hprod c c.2
    refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
    change Submodule.Quotient.mk (hg4_shapiroZ σ g ⟨a, ha⟩) =
      (Submodule.Quotient.mk c : hg_eqH1 σ g)
    apply Eq.symm
    exact (Submodule.Quotient.eq _).mpr hc

theorem hg4_cupH1_shapiro_aux {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]
    [StarRing K] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (σ : G →* Matrix ι ι K)
    (g : Fin r → G) (hprod : (List.ofFn g).prod = 1) (H : Matrix ι ι K) (hHerm : Hᴴ = H)
    (hinv : ∀ x, (σ x)ᴴ * H * σ x = H) (x y : pc_Vpar (pc_tuple σ g)) :
    hg4_cupH1 σ g H (hg4_shapiroH1 σ g x) (hg4_shapiroH1 σ g y) =
      (Fintype.card G : K) * pc_SPar (pc_tuple σ g) H x y := by
  have hprodT : (List.ofFn (pc_tuple σ g)).prod = 1 := by
    have ht : List.ofFn (pc_tuple σ g) = (List.ofFn g).map σ := by
      rw [List.map_ofFn]
      rfl
    rw [ht, ← map_list_prod, hprod, map_one]
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change hg4_cupH1 σ g H (Submodule.Quotient.mk (hg4_shapiroZ σ g a))
    (Submodule.Quotient.mk (hg4_shapiroZ σ g b)) = _
  rw [hg4_cupH1_mk_aux σ g hprod H,
    pc_SPar_mk _ H hprodT hHerm (fun i => hinv _) a b a.2 b.2]
  change hg_fundEval (hg_cup g H (hg_shapiroCochain σ g a) (hg_shapiroCochain σ g b)) = _
  rw [hg_cup_shapiro σ g H hHerm hinv]
  have hs := pc_S_skew _ H hprodT hHerm (fun i => hinv _) a b a.2 b.2
  linear_combination -(Fintype.card G : K) * hs

theorem hg4_pcS_map_aux {K L : Type*} [Field K] [StarRing K] [Field L] [StarRing L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (f : K →+* L)
    (hf : ∀ t, f (star t) = star (f t)) (T : Fin r → Matrix ι ι K) (H : Matrix ι ι K)
    (a b : Fin r → ι → K) :
    f (pc_S T H a b) =
      pc_S (fun i => (T i).map f) (H.map f) (fun i k => f (a i k)) (fun i k => f (b i k)) := by
  have hI (A : Matrix ι ι K) : (A⁻¹).map f = (A.map f)⁻¹ := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv]
    change f.mapMatrix (A.det⁻¹ • A.adjugate) =
      (f.mapMatrix A).det⁻¹ • (f.mapMatrix A).adjugate
    rw [← f.map_det, ← f.map_adjugate]
    ext i j
    change f (A.det⁻¹ * A.adjugate i j) = (f A.det)⁻¹ * f (A.adjugate i j)
    rw [map_mul, map_inv₀]
  have hmv (M : Matrix ι ι K) (v : ι → K) :
      f ∘ (M *ᵥ v) = M.map f *ᵥ (f ∘ v) := funext (f.map_mulVec M v)
  have hQ (i : Fin r) : (pc_Q T i).map f = pc_Q (fun j => (T j).map f) i := by
    change f.mapMatrix (((List.finRange r).filter (fun j => j < i)).map T).prod = _
    rw [map_list_prod]
    simp only [pc_Q, List.map_map]
    rfl
  have hC (v : Fin r → ι → K) (i : Fin r) :
      (fun k => f (pc_c T v i k)) =
        pc_c (fun j => (T j).map f) (fun j k => f (v j k)) i := by
    rw [pc_c, pc_c]
    have hm : (1 - T i).map f = 1 - (T i).map f := by
      change f.mapMatrix (1 - T i) = _
      rw [map_sub, map_one]
      rfl
    simpa only [hm, Function.comp_def] using hmv (1 - T i) (v i)
  have hF (v : Fin r → ι → K) (i : Fin r) :
      (fun k => f (pc_F T v i k)) =
        pc_F (fun j => (T j).map f) (fun j k => f (v j k)) i := by
    ext k
    simp only [pc_F, Finset.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact congrFun ((hmv (pc_Q T j) (pc_c T v j)).trans (by
      simp only [Function.comp_def, hQ, hC])) k
  simp only [pc_S, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [f.map_dotProduct]
  have hstar (v : ι → K) : f ∘ star v = star (f ∘ v) := by
    funext k
    exact hf (v k)
  rw [hstar]
  have hv : f ∘ ((pc_Q T i)⁻¹ *ᵥ pc_F T a i + a i) =
      (pc_Q (fun j => (T j).map f) i)⁻¹ *ᵥ
        pc_F (fun j => (T j).map f) (fun j k => f (a j k)) i + (fun k => f (a i k)) := by
    simp only [Function.comp_def, Pi.add_apply, map_add]
    have hm := hmv ((pc_Q T i)⁻¹) (pc_F T a i)
    simpa only [Function.comp_def, hI, hQ, hF, Pi.add_def] using congrArg
      (fun v : ι → L => v + (fun k => f (a i k))) hm
  rw [hv, hmv]
  simp only [Function.comp_def, hC]

theorem hg4_sigmaK_map_aux (x : b4b_Group) : (hg4_sigmaK x).map hp_embed = b4b_toMatrix x := by
  let e := (Submonoid.equivMapOfInjective hg4_groupK hg4_embedMatrix
    hg4_embedMatrix_injective).trans (MulEquiv.submonoidCongr hg4_groupK_map)
  have h := congrArg Subtype.val (e.apply_symm_apply x)
  exact h

theorem hg4_sigmaK_tuple_aux : pc_tuple hg4_sigmaK b4b_root = hp_rootTupleK := by
  funext j
  apply hg4_embedMatrix_injective
  exact (hg4_sigmaK_map_aux (b4b_root j)).trans (hp_rootTupleK_map_eq j).symm

theorem hg4_sigmaK_trace_aux : Matrix.trace (hg4_sigmaK (b4b_root 0)) = 3 + pc_zeta := by
  have h := congrFun hg4_sigmaK_tuple_aux 0
  change hg4_sigmaK (b4b_root 0) = hp_rootTupleK 0 at h
  rw [h]
  simp [hp_rootTupleK, hp_rootTupleOver, HodgeLean.Papers.g32R1, Matrix.trace, Fin.sum_univ_four]
  ring

end HodgeLean.Foundations.Program
