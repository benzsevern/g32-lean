import HodgeLean.Foundations.Program.PrymParabolicIntersectionWindowPaths

set_option linter.unusedSectionVars false

noncomputable section
open Set Filter Complex
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Program

/-! ## Helpers -/

theorem hga_facePt_weights (k : Fin 3) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (j : Fin 3) :
    (hga_facePt k θ).weights j =
      if j = k then 0 else if (k = 0 ∧ j = 1) ∨ (k ≠ 0 ∧ j = 0) then 1 - θ else θ := by
  unfold hga_facePt
  rw [hg5_face_w, hga_projIcc_val hθ]

theorem hga_facePt_eq {k : Fin 3} {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (a : Convexity.StdSimplex ℝ (Fin 3))
    (h : ∀ j, a.weights j =
      if j = k then 0 else if (k = 0 ∧ j = 1) ∨ (k ≠ 0 ∧ j = 0) then 1 - θ else θ) :
    a = hga_facePt k θ := by
  apply hg5_simplex_ext <;> rw [h, hga_facePt_weights k hθ]

theorem hga_facePt_of_wedge (k : Fin 3) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    hga_facePt k θ = Convexity.StdSimplex.map k.succAbove
      (Convexity.StdSimplex.homeomorphI.symm ⟨θ, hθ⟩) := by
  unfold hga_facePt
  rw [Set.projIcc_of_mem _ hθ]

theorem hga_cont_affine (A B s : ℝ) :
    Continuous (fun x : unitInterval ↦ A + (x : ℝ) * s * B) := by fun_prop

theorem hga_abs_small {x : unitInterval} : |(x : ℝ) * (1 / 1000)| ≤ 1 / 1000 := by
  rw [abs_mul, abs_of_nonneg x.2.1, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 1000)]
  nlinarith [x.2.2]

theorem hga_abs_small' {x : unitInterval} : |-(x : ℝ) * (1 / 1000)| ≤ 1 / 1000 := by
  rw [neg_mul, abs_neg]; exact hga_abs_small

theorem hga_small_mul {X c : ℝ} (hX : |X| ≤ 1 / 1000) (hc : |c| ≤ 7) :
    -7 / 1000 ≤ X * c ∧ X * c ≤ 7 / 1000 := by
  have := hga_abs_mul_le_of X c _ _ hX hc
  rw [abs_le] at this
  constructor <;> linarith [this.1, this.2]

theorem hga_line_eq (P0 y0 c X : ℝ) :
    ((P0 + 10 * X : ℝ) : ℂ) + ((y0 + c * X : ℝ) : ℂ) * I =
      ((P0 : ℝ) : ℂ) + (y0 : ℂ) * I + ((X : ℝ) : ℂ) * (I * ((c : ℂ) - 10 * I)) := by
  apply Complex.ext <;> simp <;> ring

theorem hga_line_eq' (P0 y0 c X : ℝ) :
    ((P0 + 10 * X : ℝ) : ℂ) + ((y0 - c * X : ℝ) : ℂ) * I =
      ((P0 : ℝ) : ℂ) + (y0 : ℂ) * I + ((X : ℝ) : ℂ) * (I * (-(c : ℂ) - 10 * I)) := by
  apply Complex.ext <;> simp <;> ring

theorem hga_rayE_affine (b c X : ℝ) (j : Fin 3) :
    hga_rayE b c X j = hga_rayE b c 0 j + X * (hga_rayE b c 1 j - hga_rayE b c 0 j) := by
  fin_cases j
  · simp only [Fin.zero_eta, hga_rayE_0]; ring
  · simp only [Fin.mk_one, hga_rayE_1]; ring
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, hga_rayE_2]; ring

theorem hga_rayH_affine (b c X : ℝ) (j : Fin 3) :
    hga_rayH b c X j = hga_rayH b c 0 j + X * (hga_rayH b c 1 j - hga_rayH b c 0 j) := by
  fin_cases j
  · simp only [Fin.zero_eta, hga_rayH_0]; ring
  · simp only [Fin.mk_one, hga_rayH_1]; ring
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, hga_rayH_2]; ring

theorem hga_rayF_affine (b c X : ℝ) (j : Fin 3) :
    hga_rayF b c X j = hga_rayF b c 0 j + X * (hga_rayF b c 1 j - hga_rayF b c 0 j) := by
  fin_cases j
  · simp only [Fin.zero_eta, hga_rayF_0]; ring
  · simp only [Fin.mk_one, hga_rayF_1]; ring
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, hga_rayF_2]; ring

theorem hga_ray_cont (R : ℝ → Fin 3 → ℝ)
    (hR : ∀ X j, R X j = R 0 j + X * (R 1 j - R 0 j)) (s : ℝ) (j : Fin 3) :
    Continuous fun x : unitInterval ↦ R ((x : ℝ) * s) j := by
  have : (fun x : unitInterval ↦ R ((x : ℝ) * s) j) =
      fun x : unitInterval ↦ R 0 j + (x : ℝ) * s * (R 1 j - R 0 j) := funext fun x ↦ hR _ j
  rw [this]
  fun_prop

theorem hga_ray_cont' (R : ℝ → Fin 3 → ℝ)
    (hR : ∀ X j, R X j = R 0 j + X * (R 1 j - R 0 j)) (s : ℝ) (j : Fin 3) :
    Continuous fun x : unitInterval ↦ R (-(x : ℝ) * s) j := by
  have : (fun x : unitInterval ↦ R (-(x : ℝ) * s) j) =
      fun x : unitInterval ↦ R 0 j + -(x : ℝ) * s * (R 1 j - R 0 j) := funext fun x ↦ hR _ j
  rw [this]
  fun_prop

theorem hga_rayE_img' (u p x : ℝ) (hcb : p - u ≠ 0) (a : Convexity.StdSimplex ℝ (Fin 3))
    (ha : ∀ j, a.weights j = hga_rayE (u + 11 / 2) (p + 11 / 2) x j)
    (hsmall : 0 ≤ 1 / 2 + x * ((p + 11 / 2) / 10)) :
    hg5_wedge u p a =
      ((-11 / 2 + (p + 11 / 2) / 2 + 10 * x : ℝ) : ℂ) + ((5 + (p + 11 / 2) * x : ℝ) : ℂ) * I := by
  have h := hga_rayE_img (u + 11 / 2) (p + 11 / 2) x (by intro h; apply hcb; linarith) a ha hsmall
  simpa only [add_sub_cancel_right] using h

theorem hga_rayH_img' (u p x : ℝ) (hcb : p - u ≠ 0) (a : Convexity.StdSimplex ℝ (Fin 3))
    (ha : ∀ j, a.weights j = hga_rayH (u + 11 / 2) (p + 11 / 2) x j)
    (hsmall : 0 ≤ 1 / 2 + x * ((p + 11 / 2) / 10)) :
    hg5_wedge u p a =
      ((-11 / 2 + (p + 11 / 2) / 2 + 10 * x : ℝ) : ℂ) + ((-5 - (p + 11 / 2) * x : ℝ) : ℂ) * I := by
  have h := hga_rayH_img (u + 11 / 2) (p + 11 / 2) x (by intro h; apply hcb; linarith) a ha hsmall
  simpa only [add_sub_cancel_right] using h

theorem hga_rayF_img' (u p x : ℝ) (hcb : p - u ≠ 0) (a : Convexity.StdSimplex ℝ (Fin 3))
    (ha : ∀ j, a.weights j = hga_rayF (u + 11 / 2) (p + 11 / 2) x j)
    (hsmall : 0 ≤ 1 / 2 + x * ((u + 11 / 2) / 10)) :
    hg5_wedge u p a =
      ((-11 / 2 + (u + 11 / 2) / 2 + 10 * x : ℝ) : ℂ) + ((5 + (u + 11 / 2) * x : ℝ) : ℂ) * I := by
  have h := hga_rayF_img (u + 11 / 2) (p + 11 / 2) x (by intro h; apply hcb; linarith) a ha hsmall
  simpa only [add_sub_cancel_right] using h

/-! ## The faces `e_i` (`i < 12`): two wedges, face `a₂ = 0` -/

/-- Window data on a face `a₂ = 0` shared by two wedge triangles (the edges `e_i`, `i < 12`).
Source: `hga_rayE`, `hg5_wedge_face2`. -/
def hga_specE (τo τi : hg2_Tri Unit 13) (uo ui p : ℝ)
    (hTo : ∀ a, hg5_tri τo a = ((hg5_wedge uo p a : ℂ) : OnePoint ℂ))
    (hTi : ∀ a, hg5_tri τi a = ((hg5_wedge ui p a : ℂ) : OnePoint ℂ))
    (hbo : |uo + 11 / 2| ≤ 7) (hbi : |ui + 11 / 2| ≤ 7) (hc : |p + 11 / 2| ≤ 7)
    (hgo : 1 / 2 ≤ |p - uo|) (hgi : 1 / 2 ≤ |p - ui|) (hso : p < uo) (hsi : ui < p) :
    hga_WindowSpec :=
  have hco : 1 / 2 ≤ |p + 11 / 2 - (uo + 11 / 2)| := by
    rw [show p + 11 / 2 - (uo + 11 / 2) = p - uo by ring]; exact hgo
  have hci : 1 / 2 ≤ |p + 11 / 2 - (ui + 11 / 2)| := by
    rw [show p + 11 / 2 - (ui + 11 / 2) = p - ui by ring]; exact hgi
  have hno : p + 11 / 2 - (uo + 11 / 2) ≠ 0 := by intro h; rw [h, abs_zero] at hco; norm_num at hco
  have hni : p + 11 / 2 - (ui + 11 / 2) ≠ 0 := by intro h; rw [h, abs_zero] at hci; norm_num at hci
  have sideo : ∀ x : unitInterval, (x : ℝ) * (1 / 1000) * (p + 11 / 2 - (uo + 11 / 2)) ≤ 0 :=
    fun x ↦ by nlinarith [x.2.1]
  have sidei : ∀ x : unitInterval, -(x : ℝ) * (1 / 1000) * (p + 11 / 2 - (ui + 11 / 2)) ≤ 0 :=
    fun x ↦ by nlinarith [x.2.1]
  { τo := τo, τi := τi, τe := τi, ko := 2, ki := 2, ke := 2
    s := 1 / 2, δ := 1 / 1000, η := 1 / 1000
    P := ((-11 / 2 + (p + 11 / 2) / 2 : ℝ) : ℂ) + 5 * I
    v := ((p + 11 / 2 : ℝ) : ℂ) - 10 * I
    φ := fun θ ↦ θ - 1 / 2
    Mo := hga_simplexPath (fun x j ↦ hga_rayE (uo + 11 / 2) (p + 11 / 2) ((x : ℝ) * (1 / 1000)) j)
      (hga_ray_cont _ (hga_rayE_affine _ _) _)
      (fun x j ↦ (hga_rayE_pos _ _ _ hbo hc hco hga_abs_small (sideo x) j).1)
      (fun x ↦ hga_rayE_sum _ _ _ hno)
    Mi := hga_simplexPath (fun x j ↦ hga_rayE (ui + 11 / 2) (p + 11 / 2) (-(x : ℝ) * (1 / 1000)) j)
      (hga_ray_cont' _ (hga_rayE_affine _ _) _)
      (fun x j ↦ (hga_rayE_pos _ _ _ hbi hc hci hga_abs_small' (sidei x) j).1)
      (fun x ↦ hga_rayE_sum _ _ _ hni)
    hδ := by norm_num
    hs0 := by norm_num
    hs1 := by norm_num
    hη := by norm_num
    hv := by
      intro h
      have := congrArg Complex.im h
      simp at this
    Mo0 := by
      apply hga_facePt_eq ⟨by norm_num, by norm_num⟩
      intro j
      rw [hga_simplexPath_weights]
      fin_cases j <;> simp [hga_rayE_0, hga_rayE_1, hga_rayE_2] <;> norm_num
    Mi0 := by
      apply hga_facePt_eq ⟨by norm_num, by norm_num⟩
      intro j
      rw [hga_simplexPath_weights]
      fin_cases j <;> simp [hga_rayE_0, hga_rayE_1, hga_rayE_2] <;> norm_num
    Mo_pos := fun x hx j ↦ by
      rw [hga_simplexPath_weights]
      exact (hga_rayE_pos _ _ _ hbo hc hco hga_abs_small (sideo x) j).2 (by positivity)
    Mi_pos := fun x hx j ↦ by
      rw [hga_simplexPath_weights]
      exact (hga_rayE_pos _ _ _ hbi hc hci hga_abs_small' (sidei x) j).2
        (by have : 0 < (x : ℝ) * (1 / 1000) := by positivity
            linarith)
    Mo_img := fun x ↦ by
      have hs := hga_small_mul (hga_abs_small (x := x)) hc
      rw [hTo, hga_rayE_img' uo p _ (by intro h; apply hno; linarith) _
        (fun j ↦ hga_simplexPath_weights _ _ _ _ x j) (by nlinarith)]
      congr 1
      rw [hga_line_eq]
      push_cast
      ring
    Mi_img := fun x ↦ by
      have hs := hga_small_mul (hga_abs_small' (x := x)) hc
      rw [hTi, hga_rayE_img' ui p _ (by intro h; apply hni; linarith) _
        (fun j ↦ hga_simplexPath_weights _ _ _ _ x j) (by nlinarith)]
      congr 1
      rw [hga_line_eq]
      push_cast
      ring
    E_img := fun θ hθ ↦ by
      have hθ' : θ ∈ Icc (0 : ℝ) 1 := ⟨by norm_num at hθ; linarith [hθ.1], by norm_num at hθ; linarith [hθ.2]⟩
      rw [hTi, hga_facePt_of_wedge 2 hθ', hg5_wedge_face2]
      congr 1
      apply Complex.ext <;> simp <;> ring
    φ_s := by norm_num
    φ_inj := fun a _ b _ h ↦ by simpa using h
    φ_diff := (contDiff_id.sub contDiff_const).contDiffOn
    φ_deriv := by
      rw [show (fun θ : ℝ ↦ θ - 1 / 2) = fun θ ↦ θ + (-(1 / 2)) by ext; ring, deriv_add_const,
        deriv_id'']
      norm_num
    im_dual := fun x hx ↦ by
      have hx' : |x * (1 / 1000)| ≤ 1 / 1000 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 1000)]
        nlinarith [abs_le.mpr ⟨hx.1, hx.2⟩]
      have hs := hga_small_mul hx' hc
      have e : (((-11 / 2 + (p + 11 / 2) / 2 : ℝ) : ℂ) + 5 * I +
          ((x * (1 / 1000) : ℝ) : ℂ) * (I * (((p + 11 / 2 : ℝ) : ℂ) - 10 * I))).im =
          5 + x * (1 / 1000) * (p + 11 / 2) := by simp <;> ring
      rw [e, abs_of_pos (by linarith)]
      linarith
    im_prim := fun θ hθ ↦ by
      have e : (((-11 / 2 + (p + 11 / 2) / 2 : ℝ) : ℂ) + 5 * I +
          (((θ - 1 / 2 : ℝ) : ℝ) : ℂ) * (((p + 11 / 2 : ℝ) : ℂ) - 10 * I)).im =
          5 - 10 * (θ - 1 / 2) := by simp <;> ring
      rw [e]
      norm_num at hθ
      rw [abs_of_pos (by linarith [hθ.2])]
      linarith [hθ.2] }

/-! ## The faces `h_i` (`i < 12`): two wedges, face `a₀ = 0` -/

/-- Window data on a face `a₀ = 0` shared by two wedge triangles (the edges `h_i`, `i < 12`).
Source: `hga_rayH`, `hg5_wedge_face0`. -/
def hga_specH (τo τi : hg2_Tri Unit 13) (uo ui p : ℝ)
    (hTo : ∀ a, hg5_tri τo a = ((hg5_wedge uo p a : ℂ) : OnePoint ℂ))
    (hTi : ∀ a, hg5_tri τi a = ((hg5_wedge ui p a : ℂ) : OnePoint ℂ))
    (hbo : |uo + 11 / 2| ≤ 7) (hbi : |ui + 11 / 2| ≤ 7) (hc : |p + 11 / 2| ≤ 7)
    (hgo : 1 / 2 ≤ |p - uo|) (hgi : 1 / 2 ≤ |p - ui|) (hso : p < uo) (hsi : ui < p) :
    hga_WindowSpec :=
  have hco : 1 / 2 ≤ |p + 11 / 2 - (uo + 11 / 2)| := by
    rw [show p + 11 / 2 - (uo + 11 / 2) = p - uo by ring]; exact hgo
  have hci : 1 / 2 ≤ |p + 11 / 2 - (ui + 11 / 2)| := by
    rw [show p + 11 / 2 - (ui + 11 / 2) = p - ui by ring]; exact hgi
  have hno : p + 11 / 2 - (uo + 11 / 2) ≠ 0 := by intro h; rw [h, abs_zero] at hco; norm_num at hco
  have hni : p + 11 / 2 - (ui + 11 / 2) ≠ 0 := by intro h; rw [h, abs_zero] at hci; norm_num at hci
  have sideo : ∀ x : unitInterval, (x : ℝ) * (1 / 1000) * (p + 11 / 2 - (uo + 11 / 2)) ≤ 0 :=
    fun x ↦ by nlinarith [x.2.1]
  have sidei : ∀ x : unitInterval, -(x : ℝ) * (1 / 1000) * (p + 11 / 2 - (ui + 11 / 2)) ≤ 0 :=
    fun x ↦ by nlinarith [x.2.1]
  { τo := τo, τi := τi, τe := τi, ko := 0, ki := 0, ke := 0
    s := 1 / 2, δ := 1 / 1000, η := 1 / 1000
    P := ((-11 / 2 + (p + 11 / 2) / 2 : ℝ) : ℂ) + (-5) * I
    v := -((p + 11 / 2 : ℝ) : ℂ) - 10 * I
    φ := fun θ ↦ θ - 1 / 2
    Mo := hga_simplexPath (fun x j ↦ hga_rayH (uo + 11 / 2) (p + 11 / 2) ((x : ℝ) * (1 / 1000)) j)
      (hga_ray_cont _ (hga_rayH_affine _ _) _)
      (fun x j ↦ (hga_rayH_pos _ _ _ hbo hc hco hga_abs_small (sideo x) j).1)
      (fun x ↦ hga_rayH_sum _ _ _ hno)
    Mi := hga_simplexPath (fun x j ↦ hga_rayH (ui + 11 / 2) (p + 11 / 2) (-(x : ℝ) * (1 / 1000)) j)
      (hga_ray_cont' _ (hga_rayH_affine _ _) _)
      (fun x j ↦ (hga_rayH_pos _ _ _ hbi hc hci hga_abs_small' (sidei x) j).1)
      (fun x ↦ hga_rayH_sum _ _ _ hni)
    hδ := by norm_num
    hs0 := by norm_num
    hs1 := by norm_num
    hη := by norm_num
    hv := by
      intro h
      have := congrArg Complex.im h
      simp at this
    Mo0 := by
      apply hga_facePt_eq ⟨by norm_num, by norm_num⟩
      intro j
      rw [hga_simplexPath_weights]
      fin_cases j <;> simp [hga_rayH_0, hga_rayH_1, hga_rayH_2] <;> norm_num
    Mi0 := by
      apply hga_facePt_eq ⟨by norm_num, by norm_num⟩
      intro j
      rw [hga_simplexPath_weights]
      fin_cases j <;> simp [hga_rayH_0, hga_rayH_1, hga_rayH_2] <;> norm_num
    Mo_pos := fun x hx j ↦ by
      rw [hga_simplexPath_weights]
      exact (hga_rayH_pos _ _ _ hbo hc hco hga_abs_small (sideo x) j).2 (by positivity)
    Mi_pos := fun x hx j ↦ by
      rw [hga_simplexPath_weights]
      exact (hga_rayH_pos _ _ _ hbi hc hci hga_abs_small' (sidei x) j).2
        (by have : 0 < (x : ℝ) * (1 / 1000) := by positivity
            linarith)
    Mo_img := fun x ↦ by
      have hs := hga_small_mul (hga_abs_small (x := x)) hc
      rw [hTo, hga_rayH_img' uo p _ (by intro h; apply hno; linarith) _
        (fun j ↦ hga_simplexPath_weights _ _ _ _ x j) (by nlinarith)]
      congr 1
      rw [hga_line_eq']
      push_cast
      ring
    Mi_img := fun x ↦ by
      have hs := hga_small_mul (hga_abs_small' (x := x)) hc
      rw [hTi, hga_rayH_img' ui p _ (by intro h; apply hni; linarith) _
        (fun j ↦ hga_simplexPath_weights _ _ _ _ x j) (by nlinarith)]
      congr 1
      rw [hga_line_eq']
      push_cast
      ring
    E_img := fun θ hθ ↦ by
      have hθ' : θ ∈ Icc (0 : ℝ) 1 := ⟨by norm_num at hθ; linarith [hθ.1], by norm_num at hθ; linarith [hθ.2]⟩
      rw [hTi, hga_facePt_of_wedge 0 hθ', hg5_wedge_face0]
      congr 1
      apply Complex.ext <;> simp <;> ring
    φ_s := by norm_num
    φ_inj := fun a _ b _ h ↦ by simpa using h
    φ_diff := (contDiff_id.sub contDiff_const).contDiffOn
    φ_deriv := by
      rw [show (fun θ : ℝ ↦ θ - 1 / 2) = fun θ ↦ θ + (-(1 / 2)) by ext; ring, deriv_add_const,
        deriv_id'']
      norm_num
    im_dual := fun x hx ↦ by
      have hx' : |x * (1 / 1000)| ≤ 1 / 1000 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 1000)]
        nlinarith [abs_le.mpr ⟨hx.1, hx.2⟩]
      have hs := hga_small_mul hx' hc
      have e : (((-11 / 2 + (p + 11 / 2) / 2 : ℝ) : ℂ) + (-5) * I +
          ((x * (1 / 1000) : ℝ) : ℂ) * (I * (-((p + 11 / 2 : ℝ) : ℂ) - 10 * I))).im =
          -5 - x * (1 / 1000) * (p + 11 / 2) := by simp <;> ring
      rw [e, abs_of_neg (by linarith)]
      linarith
    im_prim := fun θ hθ ↦ by
      have e : (((-11 / 2 + (p + 11 / 2) / 2 : ℝ) : ℂ) + (-5) * I +
          (((θ - 1 / 2 : ℝ) : ℝ) : ℂ) * (-((p + 11 / 2 : ℝ) : ℂ) - 10 * I)).im =
          -5 - 10 * (θ - 1 / 2) := by simp <;> ring
      rw [e]
      norm_num at hθ
      rw [abs_of_neg (by linarith [hθ.1])]
      linarith [hθ.1] }

/-! ## Ray paths and the faces `f_i` -/

/-- A ray from the face point at parameter `s` of the face `k` of the base triangle `τ`, with plane
image `P + (λ/1000) w`. Source: `hga_WindowSpec`. -/
structure hga_RayPath (τ : hg2_Tri Unit 13) (k : Fin 3) (s : ℝ) (P w : ℂ) where
  M : C(unitInterval, Convexity.StdSimplex ℝ (Fin 3))
  M0 : M 0 = hga_facePt k s
  pos : ∀ x : unitInterval, 0 < (x : ℝ) → ∀ j, 0 < (M x).weights j
  img : ∀ x : unitInterval,
    hg5_tri τ (M x) = (((P + (((x : ℝ) * (1 / 1000) : ℝ) : ℂ) * w) : ℂ) : OnePoint ℂ)

/-- The ray of a wedge triangle at the quarter point of its face `a₁ = 0`.
Source: `hga_rayF`. -/
def hga_rayF_path (τ : hg2_Tri Unit 13) (u p σ : ℝ)
    (hT : ∀ a, hg5_tri τ a = ((hg5_wedge u p a : ℂ) : OnePoint ℂ))
    (hb : |u + 11 / 2| ≤ 7) (hc : |p + 11 / 2| ≤ 7) (hg : 1 / 2 ≤ |p - u|)
    (hσ : σ = 1 ∨ σ = -1) (hside : 0 ≤ σ * (p - u)) :
    hga_RayPath τ 1 (1 / 4) (((-11 / 2 + (u + 11 / 2) / 2 : ℝ) : ℂ) + 5 * I)
      ((σ : ℂ) * (I * (((u + 11 / 2 : ℝ) : ℂ) - 10 * I))) :=
  have hcb : 1 / 2 ≤ |p + 11 / 2 - (u + 11 / 2)| := by
    rw [show p + 11 / 2 - (u + 11 / 2) = p - u by ring]; exact hg
  have hn : p + 11 / 2 - (u + 11 / 2) ≠ 0 := by intro h; rw [h, abs_zero] at hcb; norm_num at hcb
  have hX : ∀ x : unitInterval, |σ * (x : ℝ) * (1 / 1000)| ≤ 1 / 1000 := fun x ↦ by
    rw [mul_assoc, abs_mul]
    rcases hσ with rfl | rfl <;> simp only [abs_one, abs_neg, one_mul] <;> exact hga_abs_small
  have side : ∀ x : unitInterval, 0 ≤ σ * (x : ℝ) * (1 / 1000) * (p + 11 / 2 - (u + 11 / 2)) :=
    fun x ↦ by
      rw [show σ * (x : ℝ) * (1 / 1000) * (p + 11 / 2 - (u + 11 / 2)) =
        (σ * (p - u)) * ((x : ℝ) * (1 / 1000)) by ring]
      exact mul_nonneg hside (by nlinarith [x.2.1])
  { M := hga_simplexPath (fun x j ↦ hga_rayF (u + 11 / 2) (p + 11 / 2) (σ * (x : ℝ) * (1 / 1000)) j)
      (fun j ↦ (hga_ray_cont _ (hga_rayF_affine (u + 11 / 2) (p + 11 / 2)) (σ * (1 / 1000)) j).congr
        (fun x ↦ by simp only [mul_comm σ, mul_assoc]))
      (fun x j ↦ (hga_rayF_pos _ _ _ hb hc hcb (hX x) (side x) j).1)
      (fun x ↦ hga_rayF_sum _ _ _)
    M0 := by
      apply hga_facePt_eq ⟨by norm_num, by norm_num⟩
      intro j
      rw [hga_simplexPath_weights]
      fin_cases j <;> simp [hga_rayF_0, hga_rayF_1, hga_rayF_2] <;> norm_num
    pos := fun x hx j ↦ by
      rw [hga_simplexPath_weights]
      refine (hga_rayF_pos _ _ _ hb hc hcb (hX x) (side x) j).2 ?_
      rcases hσ with rfl | rfl
      · positivity
      · have : 0 < (x : ℝ) * (1 / 1000) := by positivity
        linarith
    img := fun x ↦ by
      have hs := hga_small_mul (hX x) hb
      rw [hT, hga_rayF_img' u p _ (by intro h; apply hn; linarith) _
        (fun j ↦ hga_simplexPath_weights _ _ _ _ x j) (by nlinarith)]
      congr 1
      rw [hga_line_eq]
      push_cast
      ring }

/-- Window data on a face `a₁ = 0` (the arcs `f_i`) from two rays and a wedge triangle carrying
the arc. Source: `hga_rayF`, `hga_coneRayF`, `hg5_wedge_face1`. -/
def hga_specF (τo τi τe : hg2_Tri Unit 13) (u pe : ℝ)
    (hTe : ∀ a, hg5_tri τe a = ((hg5_wedge u pe a : ℂ) : OnePoint ℂ))
    (hb : |u + 11 / 2| ≤ 7)
    (Ro : hga_RayPath τo 1 (1 / 4) (((-11 / 2 + (u + 11 / 2) / 2 : ℝ) : ℂ) + 5 * I)
      (((1 : ℝ) : ℂ) * (I * (((u + 11 / 2 : ℝ) : ℂ) - 10 * I))))
    (Ri : hga_RayPath τi 1 (1 / 4) (((-11 / 2 + (u + 11 / 2) / 2 : ℝ) : ℂ) + 5 * I)
      (((-1 : ℝ) : ℂ) * (I * (((u + 11 / 2 : ℝ) : ℂ) - 10 * I)))) :
    hga_WindowSpec where
  τo := τo
  τi := τi
  τe := τe
  ko := 1
  ki := 1
  ke := 1
  s := 1 / 4
  δ := 1 / 1000
  η := 1 / 1000
  P := ((-11 / 2 + (u + 11 / 2) / 2 : ℝ) : ℂ) + 5 * I
  v := ((u + 11 / 2 : ℝ) : ℂ) - 10 * I
  φ := fun θ ↦ 2 * θ - 1 / 2
  Mo := Ro.M
  Mi := Ri.M
  hδ := by norm_num
  hs0 := by norm_num
  hs1 := by norm_num
  hη := by norm_num
  hv := by
    intro h
    have := congrArg Complex.im h
    simp at this
  Mo0 := Ro.M0
  Mi0 := Ri.M0
  Mo_pos := Ro.pos
  Mi_pos := Ri.pos
  Mo_img := fun x ↦ by rw [Ro.img]; push_cast; ring_nf
  Mi_img := fun x ↦ by rw [Ri.img]; push_cast; ring_nf
  E_img := fun θ hθ ↦ by
    norm_num at hθ
    have hθ' : θ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    rw [hTe, hga_facePt_of_wedge 1 hθ', hg5_wedge_face1]
    rw [abs_of_pos (show (0 : ℝ) < 1 - 2 * θ by linarith [hθ.2])]
    congr 1
    apply Complex.ext <;> simp <;> ring
  φ_s := by norm_num
  φ_inj := fun a _ b _ h ↦ by simp only at h; linarith
  φ_diff := ((contDiff_const.mul contDiff_id).sub contDiff_const).contDiffOn
  φ_deriv := by
    have : HasDerivAt (fun θ : ℝ ↦ 2 * θ - 1 / 2) 2 (1 / 4) := by
      simpa using ((hasDerivAt_id (1 / 4 : ℝ)).const_mul 2).sub_const (1 / 2)
    rw [this.deriv]
    norm_num
  im_dual := fun x hx ↦ by
    have hx' : |x * (1 / 1000)| ≤ 1 / 1000 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 1000)]
      nlinarith [abs_le.mpr ⟨hx.1, hx.2⟩]
    have hs := hga_small_mul hx' hb
    have e : (((-11 / 2 + (u + 11 / 2) / 2 : ℝ) : ℂ) + 5 * I +
        ((x * (1 / 1000) : ℝ) : ℂ) * (I * (((u + 11 / 2 : ℝ) : ℂ) - 10 * I))).im =
        5 + x * (1 / 1000) * (u + 11 / 2) := by simp <;> ring
    rw [e, abs_of_pos (by linarith)]
    linarith
  im_prim := fun θ hθ ↦ by
    have e : (((-11 / 2 + (u + 11 / 2) / 2 : ℝ) : ℂ) + 5 * I +
        (((2 * θ - 1 / 2 : ℝ) : ℝ) : ℂ) * (((u + 11 / 2 : ℝ) : ℂ) - 10 * I)).im =
        5 - 10 * (2 * θ - 1 / 2) := by simp <;> ring
    rw [e]
    norm_num at hθ
    rw [abs_of_pos (by linarith [hθ.2])]
    linarith [hθ.2]

/-! ## Ray paths in the cone triangles -/

theorem hga_coneRayF_cont (b s : ℝ) (hb : |b| = 7) (hs : |s| ≤ 1 / 1000) (j : Fin 3) :
    Continuous fun x : unitInterval ↦ hga_coneRayF b ((x : ℝ) * s) j := by
  have hden : ∀ x : unitInterval, 1 + (x : ℝ) * s * (10 / b + b / 10) ≠ 0 := by
    intro x
    have hx : |(x : ℝ) * s| ≤ 1 / 1000 := by
      rw [abs_mul, abs_of_nonneg x.2.1]; nlinarith [x.2.2, abs_nonneg s]
    exact (hga_coneSF_bounds b _ hb hx).1.ne'
  have hS : Continuous fun x : unitInterval ↦ hga_coneSF b ((x : ℝ) * s) :=
    continuous_const.div (by fun_prop) hden
  fin_cases j
  · simp only [hga_coneRayF, Fin.zero_eta, Matrix.cons_val_zero]
    fun_prop
  · simp only [hga_coneRayF, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    fun_prop
  · simp only [hga_coneRayF, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    fun_prop

/-- The ray of a cone triangle at the quarter point of its face `a₁ = 0` (the arcs `f_0`, `f_12`).
Source: `hga_coneRayF`. -/
def hga_coneRayF_path (τ : hg2_Tri Unit 13) (u σ : ℝ)
    (hT : ∀ a, hg5_tri τ a = hg5_chartInv (hg5_coneFun (2 * (u + 11 / 2)) a))
    (hb : |u + 11 / 2| = 7) (hσ : σ = 1 ∨ σ = -1) (hside : 0 ≤ σ * (u + 11 / 2)) :
    hga_RayPath τ 1 (1 / 4) (((-11 / 2 + (u + 11 / 2) / 2 : ℝ) : ℂ) + 5 * I)
      ((σ : ℂ) * (I * (((u + 11 / 2 : ℝ) : ℂ) - 10 * I))) :=
  have hs : |σ * (1 / 1000)| ≤ 1 / 1000 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hX : ∀ x : unitInterval, |(x : ℝ) * (σ * (1 / 1000))| ≤ 1 / 1000 := fun x ↦ by
    rw [abs_mul, abs_of_nonneg x.2.1]; nlinarith [x.2.2, abs_nonneg (σ * (1 / 1000))]
  have side : ∀ x : unitInterval, 0 ≤ (x : ℝ) * (σ * (1 / 1000)) * (u + 11 / 2) := fun x ↦ by
    rw [show (x : ℝ) * (σ * (1 / 1000)) * (u + 11 / 2) = (σ * (u + 11 / 2)) * ((x : ℝ) / 1000) by
      ring]
    exact mul_nonneg hside (by have := x.2.1; positivity)
  { M := hga_simplexPath (fun x j ↦ hga_coneRayF (u + 11 / 2) ((x : ℝ) * (σ * (1 / 1000))) j)
      (fun j ↦ hga_coneRayF_cont _ _ hb hs j)
      (fun x j ↦ (hga_coneRayF_pos _ _ hb (hX x) (side x) j).1)
      (fun x ↦ hga_coneRayF_sum _ _)
    M0 := by
      apply hga_facePt_eq ⟨by norm_num, by norm_num⟩
      intro j
      rw [hga_simplexPath_weights]
      fin_cases j <;> simp [hga_coneRayF, hga_coneSF] <;> norm_num
    pos := fun x hx j ↦ by
      rw [hga_simplexPath_weights]
      refine (hga_coneRayF_pos _ _ hb (hX x) (side x) j).2 ?_
      rcases hσ with rfl | rfl <;> positivity
    img := fun x ↦ by
      rw [hT, hga_coneRayF_img _ _ hb (hX x) _ (fun j ↦ hga_simplexPath_weights _ _ _ _ x j)]
      congr 1
      rw [hga_line_eq]
      push_cast
      ring }

theorem hga_coneRay_S_cont (k s : ℝ) (hk : |k| = 14) (hs : |s| ≤ 1 / 1000) :
    Continuous fun x : unitInterval ↦ hga_coneS k ((x : ℝ) * s) := by
  have hden : ∀ x : unitInterval, 2 - 2 * ((x : ℝ) * s) / k ≠ 0 := by
    intro x
    have hx : |(x : ℝ) * s| ≤ 1 / 1000 := by
      rw [abs_mul, abs_of_nonneg x.2.1]; nlinarith [x.2.2, abs_nonneg s]
    have h := (hga_coneS_pos k _ hk hx).1
    intro h0
    rw [hga_coneS, h0, div_zero] at h
    exact lt_irrefl _ h
  exact continuous_const.div (by fun_prop) hden

/-- The ray of a cone triangle at the midpoint of its face `a₂ = 0` (the ray `e_12`).
Source: `hga_coneRayE`. -/
def hga_coneRayE_path (τ : hg2_Tri Unit 13) (k σ : ℝ)
    (hT : ∀ a, hg5_tri τ a = hg5_chartInv (hg5_coneFun k a))
    (hk : |k| = 14) (hσ : σ = 1 ∨ σ = -1) (hside : σ * k ≤ 0) :
    hga_RayPath τ 2 (1 / 2) (((-11 / 2 : ℝ) : ℂ) + 20 * I) ((σ : ℂ) * (I * I)) :=
  have hs : |σ * (1 / 1000)| ≤ 1 / 1000 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hX : ∀ x : unitInterval, |(x : ℝ) * (σ * (1 / 1000))| ≤ 1 / 1000 := fun x ↦ by
    rw [abs_mul, abs_of_nonneg x.2.1]; nlinarith [x.2.2, abs_nonneg (σ * (1 / 1000))]
  have side : ∀ x : unitInterval, (x : ℝ) * (σ * (1 / 1000)) * k ≤ 0 := fun x ↦ by
    rw [show (x : ℝ) * (σ * (1 / 1000)) * k = (σ * k) * ((x : ℝ) / 1000) by ring]
    exact mul_nonpos_of_nonpos_of_nonneg hside (by have := x.2.1; positivity)
  have hSc := hga_coneRay_S_cont k _ hk hs
  { M := hga_simplexPath (fun x j ↦ hga_coneRayE k ((x : ℝ) * (σ * (1 / 1000))) j)
      (fun j ↦ by
        fin_cases j
        · simp only [hga_coneRayE, Fin.zero_eta, Matrix.cons_val_zero]; fun_prop
        · simp only [hga_coneRayE, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]; fun_prop
        · simp only [hga_coneRayE, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
            Matrix.head_cons]; fun_prop)
      (fun x j ↦ (hga_coneRayE_pos _ _ hk (hX x) (side x) j).1)
      (fun x ↦ hga_coneRayE_sum _ _)
    M0 := by
      apply hga_facePt_eq ⟨by norm_num, by norm_num⟩
      intro j
      rw [hga_simplexPath_weights]
      fin_cases j <;> simp [hga_coneRayE, hga_coneS] <;> norm_num
    pos := fun x hx j ↦ by
      rw [hga_simplexPath_weights]
      refine (hga_coneRayE_pos _ _ hk (hX x) (side x) j).2 ?_
      rcases hσ with rfl | rfl <;> positivity
    img := fun x ↦ by
      rw [hT, hga_coneRayE_img _ _ hk (hX x) _ (fun j ↦ hga_simplexPath_weights _ _ _ _ x j)]
      congr 1
      apply Complex.ext <;> simp <;> ring }

/-- The ray of a cone triangle at the midpoint of its face `a₀ = 0` (the ray `h_12`).
Source: `hga_coneRayH`. -/
def hga_coneRayH_path (τ : hg2_Tri Unit 13) (k σ : ℝ)
    (hT : ∀ a, hg5_tri τ a = hg5_chartInv (hg5_coneFun k a))
    (hk : |k| = 14) (hσ : σ = 1 ∨ σ = -1) (hside : σ * k ≤ 0) :
    hga_RayPath τ 0 (1 / 2) (((-11 / 2 : ℝ) : ℂ) + (-20) * I) ((σ : ℂ) * (I * I)) :=
  have hs : |σ * (1 / 1000)| ≤ 1 / 1000 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hX : ∀ x : unitInterval, |(x : ℝ) * (σ * (1 / 1000))| ≤ 1 / 1000 := fun x ↦ by
    rw [abs_mul, abs_of_nonneg x.2.1]; nlinarith [x.2.2, abs_nonneg (σ * (1 / 1000))]
  have side : ∀ x : unitInterval, (x : ℝ) * (σ * (1 / 1000)) * k ≤ 0 := fun x ↦ by
    rw [show (x : ℝ) * (σ * (1 / 1000)) * k = (σ * k) * ((x : ℝ) / 1000) by ring]
    exact mul_nonpos_of_nonpos_of_nonneg hside (by have := x.2.1; positivity)
  have hSc := hga_coneRay_S_cont k _ hk hs
  { M := hga_simplexPath (fun x j ↦ hga_coneRayH k ((x : ℝ) * (σ * (1 / 1000))) j)
      (fun j ↦ by
        fin_cases j
        · simp only [hga_coneRayH, Fin.zero_eta, Matrix.cons_val_zero]; fun_prop
        · simp only [hga_coneRayH, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]; fun_prop
        · simp only [hga_coneRayH, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
            Matrix.head_cons]; fun_prop)
      (fun x j ↦ (hga_coneRayH_pos _ _ hk (hX x) (side x) j).1)
      (fun x ↦ hga_coneRayH_sum _ _)
    M0 := by
      apply hga_facePt_eq ⟨by norm_num, by norm_num⟩
      intro j
      rw [hga_simplexPath_weights]
      fin_cases j <;> simp [hga_coneRayH, hga_coneS] <;> norm_num
    pos := fun x hx j ↦ by
      rw [hga_simplexPath_weights]
      refine (hga_coneRayH_pos _ _ hk (hX x) (side x) j).2 ?_
      rcases hσ with rfl | rfl <;> positivity
    img := fun x ↦ by
      rw [hT, hga_coneRayH_img _ _ hk (hX x) _ (fun j ↦ hga_simplexPath_weights _ _ _ _ x j)]
      congr 1
      apply Complex.ext <;> simp <;> ring }

/-! ## The rays `e_12`, `h_12` between the two cones -/

theorem hga_neg_I_mul_inv (r : ℝ) : (-I * (r : ℂ))⁻¹ = I * (r : ℂ)⁻¹ := by
  rw [mul_inv, inv_neg, Complex.inv_I, neg_neg]

theorem hga_I_mul_inv (r : ℝ) : (I * (r : ℂ))⁻¹ = -I * (r : ℂ)⁻¹ := by
  rw [mul_inv, Complex.inv_I]

/-- Window data on the ray `e_12` between the two cones.
Source: `hga_coneRayE`, `hg5_coneFun_face2`. -/
def hga_specEc (τo τi : hg2_Tri Unit 13)
    (hTe : ∀ a, hg5_tri τi a = hg5_chartInv (hg5_coneFun 14 a))
    (Ro : hga_RayPath τo 2 (1 / 2) (((-11 / 2 : ℝ) : ℂ) + 20 * I) (((1 : ℝ) : ℂ) * (I * I)))
    (Ri : hga_RayPath τi 2 (1 / 2) (((-11 / 2 : ℝ) : ℂ) + 20 * I) (((-1 : ℝ) : ℂ) * (I * I))) :
    hga_WindowSpec where
  τo := τo
  τi := τi
  τe := τi
  ko := 2
  ki := 2
  ke := 2
  s := 1 / 2
  δ := 1 / 1000
  η := 1 / 1000
  P := ((-11 / 2 : ℝ) : ℂ) + 20 * I
  v := I
  φ := fun θ ↦ 10 / (1 - θ) - 20
  Mo := Ro.M
  Mi := Ri.M
  hδ := by norm_num
  hs0 := by norm_num
  hs1 := by norm_num
  hη := by norm_num
  hv := I_ne_zero
  Mo0 := Ro.M0
  Mi0 := Ri.M0
  Mo_pos := Ro.pos
  Mi_pos := Ri.pos
  Mo_img := fun x ↦ by rw [Ro.img]; push_cast; ring_nf
  Mi_img := fun x ↦ by rw [Ri.img]; push_cast; ring_nf
  E_img := fun θ hθ ↦ by
    norm_num at hθ
    have hθ' : θ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hr : (1 - θ) / 10 ≠ 0 := by
      have : 0 < 1 - θ := by linarith [hθ.2]
      positivity
    have hne : -I * (((1 - θ) / 10 : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (by exact_mod_cast hr)
    rw [hTe, hga_facePt_of_wedge 2 hθ', hg5_coneFun_face2, hg5_chartInv_ne hne, hga_neg_I_mul_inv,
      mr_centre]
    congr 1
    have h1 : (1 - θ) ≠ 0 := by intro h; apply hr; rw [h]; norm_num
    have h1' : ((1 - θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1
    push_cast
    field_simp
    ring
  φ_s := by norm_num
  φ_inj := fun a ha b hb h ↦ by
    norm_num at ha hb
    simp only at h
    have h1 : 1 - a ≠ 0 := by linarith [ha.2]
    have h2 : 1 - b ≠ 0 := by linarith [hb.2]
    field_simp at h
    linarith
  φ_diff := by
    apply ContDiffOn.sub _ contDiffOn_const
    apply contDiffOn_const.div (contDiffOn_const.sub contDiffOn_id)
    intro x hx
    norm_num at hx
    exact sub_ne_zero.mpr (by linarith [hx.2] : x < 1).ne'
  φ_deriv := by
    have h : HasDerivAt (fun θ : ℝ ↦ 10 / (1 - θ) - 20)
        ((0 * (1 - 1 / 2) - 10 * (-1)) / (1 - 1 / 2) ^ 2) (1 / 2) :=
      ((hasDerivAt_const (1 / 2 : ℝ) (10 : ℝ)).div
        ((hasDerivAt_id (1 / 2 : ℝ)).const_sub 1) (by norm_num)).sub_const 20
    rw [h.deriv]
    norm_num
  im_dual := fun x _ ↦ by
    have e : (((-11 / 2 : ℝ) : ℂ) + 20 * I + ((x * (1 / 1000) : ℝ) : ℂ) * (I * I)).im = 20 := by
      simp
    rw [e]
    norm_num
  im_prim := fun θ hθ ↦ by
    norm_num at hθ
    have e : (((-11 / 2 : ℝ) : ℂ) + 20 * I + (((10 / (1 - θ) - 20 : ℝ) : ℝ) : ℂ) * I).im =
        10 / (1 - θ) := by
      generalize hq : 10 / (1 - θ) - 20 = q
      simp
      linarith
    rw [e, abs_of_pos (div_pos (by norm_num) (by linarith [hθ.2]))]
    rw [le_div_iff₀ (by linarith [hθ.2])]
    linarith [hθ.1]

/-- Window data on the ray `h_12` between the two cones.
Source: `hga_coneRayH`, `hg5_coneFun_face0`. -/
def hga_specHc (τo τi : hg2_Tri Unit 13)
    (hTe : ∀ a, hg5_tri τi a = hg5_chartInv (hg5_coneFun 14 a))
    (Ro : hga_RayPath τo 0 (1 / 2) (((-11 / 2 : ℝ) : ℂ) + (-20) * I) (((1 : ℝ) : ℂ) * (I * I)))
    (Ri : hga_RayPath τi 0 (1 / 2) (((-11 / 2 : ℝ) : ℂ) + (-20) * I)
      (((-1 : ℝ) : ℂ) * (I * I))) :
    hga_WindowSpec where
  τo := τo
  τi := τi
  τe := τi
  ko := 0
  ki := 0
  ke := 0
  s := 1 / 2
  δ := 1 / 1000
  η := 1 / 1000
  P := ((-11 / 2 : ℝ) : ℂ) + (-20) * I
  v := I
  φ := fun θ ↦ 20 - 10 / θ
  Mo := Ro.M
  Mi := Ri.M
  hδ := by norm_num
  hs0 := by norm_num
  hs1 := by norm_num
  hη := by norm_num
  hv := I_ne_zero
  Mo0 := Ro.M0
  Mi0 := Ri.M0
  Mo_pos := Ro.pos
  Mi_pos := Ri.pos
  Mo_img := fun x ↦ by rw [Ro.img]; push_cast; ring_nf
  Mi_img := fun x ↦ by rw [Ri.img]; push_cast; ring_nf
  E_img := fun θ hθ ↦ by
    norm_num at hθ
    have hθ' : θ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hr : θ / 10 ≠ 0 := by
      have : 0 < θ := by linarith [hθ.1]
      positivity
    have hne : I * ((θ / 10 : ℝ) : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hr)
    rw [hTe, hga_facePt_of_wedge 0 hθ', hg5_coneFun_face0]
    rw [show ((⟨θ, hθ'⟩ : unitInterval) : ℝ) = θ from rfl]
    rw [hg5_chartInv_ne hne, hga_I_mul_inv, mr_centre]
    congr 1
    have h1 : θ ≠ 0 := by intro h; apply hr; rw [h]; norm_num
    have h1' : ((θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1
    push_cast
    field_simp
    ring
  φ_s := by norm_num
  φ_inj := fun a ha b hb h ↦ by
    norm_num at ha hb
    simp only at h
    have h1 : a ≠ 0 := by linarith [ha.1]
    have h2 : b ≠ 0 := by linarith [hb.1]
    field_simp at h
    linarith
  φ_diff := by
    apply contDiffOn_const.sub
    apply contDiffOn_const.div contDiffOn_id
    intro x hx
    norm_num at hx
    exact (by linarith [hx.1] : (0 : ℝ) < x).ne'
  φ_deriv := by
    have h : HasDerivAt (fun θ : ℝ ↦ 20 - 10 / θ)
        (-((0 * (1 / 2) - 10 * 1) / (1 / 2) ^ 2)) (1 / 2) :=
      ((hasDerivAt_const (1 / 2 : ℝ) (10 : ℝ)).div (hasDerivAt_id (1 / 2 : ℝ))
        (by norm_num)).const_sub 20
    rw [h.deriv]
    norm_num
  im_dual := fun x _ ↦ by
    have e : (((-11 / 2 : ℝ) : ℂ) + (-20) * I + ((x * (1 / 1000) : ℝ) : ℂ) * (I * I)).im = -20 := by
      simp
    rw [e]
    norm_num
  im_prim := fun θ hθ ↦ by
    norm_num at hθ
    have e : (((-11 / 2 : ℝ) : ℂ) + (-20) * I + (((20 - 10 / θ : ℝ) : ℝ) : ℂ) * I).im =
        -(10 / θ) := by
      generalize hq : 20 - 10 / θ = q
      simp
      linarith
    rw [e, abs_neg, abs_of_pos (div_pos (by norm_num) (by linarith [hθ.1]))]
    rw [le_div_iff₀ (by linarith [hθ.1])]
    linarith [hθ.2]

end HodgeLean.Foundations.Program
