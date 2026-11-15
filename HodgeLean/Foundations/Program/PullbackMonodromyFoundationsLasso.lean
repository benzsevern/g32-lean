import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsTransport
import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsReflection
import HodgeLean.Foundations.Program.RigidStartingSystem

/-! # A conjugate of the first reflection in the pullback representation

A lasso around a simple root over five, inside the path-connected regular domain.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65t_reflection_in_image_proof (x : b65s_regular)
    (ρ : FundamentalGroup b65s_regular x →* b4b_Group)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hρ : ∀ γ : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val) =
        (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
          b65r_operator (b4b_toMatrix (ρ (FundamentalGroup.fromPath ⟦γ⟧))) * ↑(C⁻¹)) :
    ∃ g : b4b_Group, g * b4b_generators 0 * g⁻¹ ∈ ρ.range := by
  obtain ⟨a, ha⟩ := b65t_P5_root
  have ha0 : a ≠ 0 := by rintro rfl; norm_num [b65r_P] at ha
  have ha3 : a ≠ 3 := by rintro rfl; norm_num [b65r_P] at ha
  have ha1 : a ≠ 1 := by rintro rfl; norm_num [b65r_P] at ha
  have ha2 : a ≠ -2 := by rintro rfl; norm_num [b65r_P] at ha
  obtain ⟨r, hr, hloc⟩ := b65r_pullback_local_monodromy a
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
  have htarget : b65r_localTarget a = b4b_generators 0 := by
    have h12 : ¬(a = 1 ∨ a = -2) := by tauto
    simp [b65r_localTarget, ha0, ha3, h12, ha]
  -- a punctured disc about `a` inside the regular domain
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ z, dist z a < ε → z ≠ a → z ∈ b65s_regular := by
    have hT : IsClosed (b65t_bad \ {a}) := (b65t_bad_finite.sdiff).isClosed
    have haT : a ∈ (b65t_bad \ {a})ᶜ := by simp
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hT.isOpen_compl a haT
    refine ⟨ε, hε, fun z hz hza ↦ ?_⟩
    have := hsub (mem_ball.mpr hz)
    rw [b65t_regular_eq]
    intro hzb
    exact this ⟨hzb, hza⟩
  set ρ' := min r ε / 2 with hρ'
  have hρ0 : 0 < ρ' := by positivity
  have hρr : ρ' < r := by rw [hρ']; linarith [min_le_left r ε]
  have hρε : ρ' < ε := by rw [hρ']; linarith [min_le_right r ε]
  have hcirc : ∀ t, b65f_circle a ρ' t ∈ b65s_regular := by
    intro t
    have hn := b65f_circle_norm a ρ' t
    rw [abs_of_pos hρ0] at hn
    apply hball
    · rw [dist_eq_norm, hn]; exact hρε
    · intro h
      rw [h, sub_self, norm_zero] at hn
      exact hρ0.ne hn
  obtain ⟨K, hK⟩ := hloc ρ' hρ0 hρr
  rw [htarget] at hK
  let y : b65s_regular := ⟨b65f_circle a ρ' 0, hcirc 0⟩
  let c : Path y y :=
    { toFun := fun t ↦ ⟨b65f_circle a ρ' t, hcirc t⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        unfold b65f_circle
        fun_prop
      source' := by simp [y]
      target' := by
        apply Subtype.ext
        simp only [Set.Icc.coe_one, y]
        exact b65f_circle_one_eq_zero a ρ' }
  have hTc : b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (c.extend t).val) =
      b65f_transport (Fin 4 → ℂ) b65r_pullback (b65f_circle a ρ') := by
    apply b65t_transport_congr_Icc
    intro t ht
    simp only [Path.extend_apply c ht]
    rfl
  have : PathConnectedSpace b65s_regular :=
    isPathConnected_iff_pathConnectedSpace.mp b65t_regular_pathConnected
  let δ : Path x y := PathConnectedSpace.somePath x y
  let T : ∀ {p q : b65s_regular}, Path p q → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) :=
    fun γ ↦ b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val)
  have hcomp : ∀ {p q s : b65s_regular} (γ : Path p q) (γ' : Path q s),
      T (γ.trans γ') = T γ' * T γ := fun γ γ' ↦
    b65f_path_composition (Fin 4 → ℂ) _ b65t_regular_open _ b65t_pullback_analytic _ _ _ γ γ'
  have hrefl : ∀ {p q : b65s_regular} (γ : Path p q), T (γ.trans γ.symm) = 1 := by
    intro p q γ
    rw [show T (γ.trans γ.symm) = T (Path.refl p) from
      (b65f_homotopy_invariance (Fin 4 → ℂ) _ b65t_regular_open _ b65t_pullback_analytic _ _ _ _
        ⟨Path.Homotopy.reflTransSymm γ⟩).symm]
    exact b65t_transport_refl _ p
  have h1 : T δ.symm * T δ = 1 := by rw [← hcomp]; exact hrefl δ
  have h2 : T δ * T δ.symm = 1 := by
    rw [← hcomp]
    have := hrefl δ.symm
    rwa [Path.symm_symm] at this
  let Uu : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ := ⟨T δ.symm, T δ, h1, h2⟩
  let ℓ : Path x x := (δ.trans c).trans δ.symm
  have hℓ : T ℓ = (Uu : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) * (K : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
      b65r_operator (b4b_toMatrix (b4b_generators 0)) * ↑(K⁻¹) * ↑(Uu⁻¹) := by
    change T ℓ = T δ.symm * _ * _ * _ * T δ
    rw [hcomp, hcomp, show T c = _ from hTc, hK]
    simp only [mul_assoc]
  have hX := hρ ℓ
  set g := ρ (FundamentalGroup.fromPath ⟦ℓ⟧)
  let K' := C⁻¹ * Uu * K
  have hconj : b65r_operator (b4b_toMatrix g) =
      (K' : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
        b65r_operator (b4b_toMatrix (b4b_generators 0)) * ↑(K'⁻¹) := by
    have e : b65r_operator (b4b_toMatrix g) =
        ↑(C⁻¹) * ((C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) * b65r_operator (b4b_toMatrix g) *
          ↑(C⁻¹)) * (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) := by
      simp only [mul_assoc, Units.inv_mul, mul_one]
      simp only [← mul_assoc, Units.inv_mul, one_mul]
    rw [e, ← hX]
    change ↑(C⁻¹) * T ℓ * ↑C = _
    rw [hℓ]
    simp only [K', mul_inv_rev, Units.val_mul, mul_assoc, inv_inv]
  obtain ⟨h, hh⟩ := b65t_reflection_class_proof g K' hconj
  exact ⟨h, hh ▸ ⟨_, rfl⟩⟩

end HodgeLean.Foundations.Program
