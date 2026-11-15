import HodgeLean.Foundations.Program.PrymParabolicIntersectionFaces

noncomputable section
open CategoryTheory AlgebraicTopology.Singular Convexity Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem hga_positive_barycentric_mass (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) :
    0 < ∑ i, max (w i) 0 := by
  have h : (∑ i, w i) ≤ ∑ i, max (w i) 0 :=
    Finset.sum_le_sum (fun i _ ↦ le_max_left (w i) 0)
  rw [hw] at h
  linarith

/-- Normalization of the positive barycentric weights to a point of the triangle.
Source: Mathlib `Convexity.StdSimplex`; the sum of the input weights is one. -/
def hga_normalize_barycentric (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) :
    StdSimplex ℝ (Fin 3) where
  weights := Finsupp.equivFunOnFinite.symm
    (fun i ↦ max (w i) 0 / (∑ j, max (w j) 0))
  nonneg := by
    intro i
    change 0 ≤ max (w i) 0 / (∑ j, max (w j) 0)
    exact div_nonneg (le_max_right _ _) (hga_positive_barycentric_mass w hw).le
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp_rw [Finsupp.coe_equivFunOnFinite_symm]
    rw [← Finset.sum_div, div_self (hga_positive_barycentric_mass w hw).ne']

theorem hga_normalize_barycentric_nonnegative (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1)
    (h0 : ∀ i, 0 ≤ w i) (i : Fin 3) :
    (hga_normalize_barycentric w hw).weights i = w i := by
  simp only [hga_normalize_barycentric, Finsupp.coe_equivFunOnFinite_symm]
  have hm : ∀ j, max (w j) 0 = w j := fun j ↦ max_eq_left (h0 j)
  simp_rw [hm]
  rw [hw, div_one]

theorem hga_normalize_barycentric_interior (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, 0 < b.weights i)
    (heq : hga_normalize_barycentric w hw = b) : ∀ i, w i = b.weights i := by
  have hp (i : Fin 3) : 0 < w i := by
    by_contra h
    have hle : w i ≤ 0 := le_of_not_gt h
    have he := congrArg (fun a : StdSimplex ℝ (Fin 3) ↦ a.weights i) heq
    simp only [hga_normalize_barycentric, Finsupp.coe_equivFunOnFinite_symm,
      max_eq_right hle, zero_div] at he
    have hi := hb i
    linarith
  intro i
  have he := congrArg (fun a : StdSimplex ℝ (Fin 3) ↦ a.weights i) heq
  rw [hga_normalize_barycentric_nonnegative w hw (fun j ↦ (hp j).le) i] at he
  exact he

theorem hga_continuous_normalize_barycentric {X : Type} [TopologicalSpace X]
    (w : X → Fin 3 → ℝ) (hw : ∀ x, ∑ i, w x i = 1)
    (hc : ∀ i, Continuous (fun x ↦ w x i)) :
    Continuous (fun x ↦ hga_normalize_barycentric (w x) (hw x)) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)).continuous_iff]
  apply continuous_pi
  intro i
  simp only [Function.comp_apply, hga_normalize_barycentric, Finsupp.coe_equivFunOnFinite_symm]
  have hd : Continuous (fun x ↦ ∑ j, max (w x j) 0) :=
    continuous_finset_sum _ (fun j _ ↦ (hc j).max continuous_const)
  exact ((hc i).max continuous_const).div hd
    (fun x ↦ (hga_positive_barycentric_mass (w x) (hw x)).ne')

/-- Retraction of the complex coordinate plane to the triangle, centred at its barycentre.
Source: Hatcher, *Algebraic Topology*, §2.1, barycentric coordinates;
`hga_normalize_barycentric`. -/
def hga_triangleRetraction (z : ℂ) : StdSimplex ℝ (Fin 3) :=
  hga_normalize_barycentric
    ![(1 : ℝ) / 3 - z.re - z.im, 1 / 3 + z.re, 1 / 3 + z.im]
    (by simp [Fin.sum_univ_three] <;> ring)

/-- Complex affine coordinate on the triangle, centred at its barycentre.
Source: Hatcher, *Algebraic Topology*, §2.1, barycentric coordinates. -/
def hga_triangleCoordinate (a : StdSimplex ℝ (Fin 3)) : ℂ :=
  (((a.weights 1 - 1 / 3 : ℝ) : ℂ)) + (((a.weights 2 - 1 / 3 : ℝ) : ℂ)) * Complex.I

theorem hga_triangleRetraction_coordinate (a : StdSimplex ℝ (Fin 3)) :
    hga_triangleRetraction (hga_triangleCoordinate a) = a := by
  let w : Fin 3 → ℝ :=
    ![(1 : ℝ) / 3 - (hga_triangleCoordinate a).re - (hga_triangleCoordinate a).im,
      1 / 3 + (hga_triangleCoordinate a).re, 1 / 3 + (hga_triangleCoordinate a).im]
  have hw : w = (fun i ↦ a.weights i) := by
    funext i
    fin_cases i <;> simp [w, hga_triangleCoordinate] <;> linarith [hg5_sum3 a]
  have hw1 : ∑ i, w i = 1 := by rw [hw]; exact a.total_of_fintype
  have h0 : ∀ i, 0 ≤ w i := by rw [hw]; exact fun i ↦ a.weights_nonneg i
  apply StdSimplex.ext
  ext i
  exact (hga_normalize_barycentric_nonnegative w hw1 h0 i).trans (congrFun hw i)

theorem hga_continuous_triangleRetraction : Continuous hga_triangleRetraction := by
  unfold hga_triangleRetraction
  apply hga_continuous_normalize_barycentric
  intro i
  fin_cases i <;> dsimp <;> fun_prop

theorem hga_triangleRetraction_barycentre_iff (b : StdSimplex ℝ (Fin 3))
    (hb : ∀ i, b.weights i = 1 / 3) (z : ℂ) :
    hga_triangleRetraction z = b ↔ z = 0 := by
  constructor
  · intro he
    have hp : ∀ i, 0 < b.weights i := by
      intro i
      rw [hb i]
      norm_num
    unfold hga_triangleRetraction at he
    have hi := hga_normalize_barycentric_interior _ _ b hp he
    have h1 : (1 : ℝ) / 3 + z.re = 1 / 3 := by simpa [hb] using hi (1 : Fin 3)
    have h2 : (1 : ℝ) / 3 + z.im = 1 / 3 := by simpa [hb] using hi (2 : Fin 3)
    apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im] <;> linarith
  · rintro rfl
    have hc : hga_triangleCoordinate b = 0 := by simp [hga_triangleCoordinate, hb]
    simpa only [hc] using hga_triangleRetraction_coordinate b

/-- Extension of a continuous triangle to the plane by barycentric retraction.
Source: `hga_triangleRetraction`, `hga_continuous_triangleRetraction`. -/
def hga_triangleExtension {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) : C(ℂ, T) :=
  σ.comp ⟨hga_triangleRetraction, hga_continuous_triangleRetraction⟩

theorem hga_triangleExtension_coordinate {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (a : StdSimplex ℝ (Fin 3)) :
    hga_triangleExtension σ (hga_triangleCoordinate a) = σ a :=
  congrArg σ (hga_triangleRetraction_coordinate a)

theorem hga_triangleExtension_barycentre_iff {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3) (z : ℂ) :
    hga_triangleExtension σ z = σ b ↔ z = 0 := by
  change σ (hga_triangleRetraction z) = σ b ↔ z = 0
  constructor
  · intro h
    exact (hga_triangleRetraction_barycentre_iff b hb z).mp (hσ h)
  · intro h
    exact congrArg σ ((hga_triangleRetraction_barycentre_iff b hb z).mpr h)

/-- The extended triangle as a map of complements of the centre points.
Source: Hatcher, *Algebraic Topology*, §3.3, maps of local homology pairs;
`hga_triangleExtension_barycentre_iff`. -/
def hga_triangleExtension_pairMap {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (hσ : Function.Injective σ)
    (b : StdSimplex ℝ (Fin 3)) (hb : ∀ i, b.weights i = 1 / 3) :
    pointComplementPair (0 : ℂ) ⟶ pointComplementPair (σ b) :=
  TopPair.ofSubsetHom (TopCat.ofHom (hga_triangleExtension σ)) (by
    intro z hz
    change hga_triangleExtension σ z ≠ σ b
    intro h
    exact hz ((hga_triangleExtension_barycentre_iff σ hσ b hb z).mp h))

theorem hga_triangleExtension_eventually_affine {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (e : T → ℂ) (z : ℂ) (ρ : ℝ)
    (hσ : ∀ a, e (σ a) = z + (ρ : ℂ) *
      (((a.weights 1 : ℝ) : ℂ) + ((a.weights 2 : ℝ) : ℂ) * Complex.I)) :
    ∀ᶠ w : ℂ in 𝓝 0, e (hga_triangleExtension σ w) =
      z + (ρ : ℂ) * ((1 : ℂ) / 3 + (1 : ℂ) / 3 * Complex.I + w) := by
  have hc0 : Continuous (fun w : ℂ ↦ (1 : ℝ) / 3 - w.re - w.im) := by fun_prop
  have hc1 : Continuous (fun w : ℂ ↦ (1 : ℝ) / 3 + w.re) := by fun_prop
  have hc2 : Continuous (fun w : ℂ ↦ (1 : ℝ) / 3 + w.im) := by fun_prop
  have h0 := (isOpen_lt continuous_const hc0).mem_nhds
    (show (0 : ℝ) < (1 : ℝ) / 3 - (0 : ℂ).re - (0 : ℂ).im by norm_num)
  have h1 := (isOpen_lt continuous_const hc1).mem_nhds
    (show (0 : ℝ) < (1 : ℝ) / 3 + (0 : ℂ).re by norm_num)
  have h2 := (isOpen_lt continuous_const hc2).mem_nhds
    (show (0 : ℝ) < (1 : ℝ) / 3 + (0 : ℂ).im by norm_num)
  filter_upwards [h0, h1, h2] with w hw0 hw1 hw2
  let v : Fin 3 → ℝ := ![(1 : ℝ) / 3 - w.re - w.im, 1 / 3 + w.re, 1 / 3 + w.im]
  have hv : ∑ i, v i = 1 := by simp [v, Fin.sum_univ_three] <;> ring
  have hv0 : ∀ i, 0 ≤ v i := by
    intro i
    fin_cases i
    · exact hw0.le
    · exact hw1.le
    · exact hw2.le
  have hw1' : (hga_triangleRetraction w).weights 1 = 1 / 3 + w.re :=
    hga_normalize_barycentric_nonnegative v hv hv0 1
  have hw2' : (hga_triangleRetraction w).weights 2 = 1 / 3 + w.im :=
    hga_normalize_barycentric_nonnegative v hv hv0 2
  change e (σ (hga_triangleRetraction w)) = _
  rw [hσ, hw1', hw2']
  push_cast
  linear_combination (ρ : ℂ) * (Complex.re_add_im w)

set_option backward.isDefEq.respectTransparency false in
theorem hga_triangleExtension_hasDerivAt {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (e : T → ℂ) (z : ℂ) (ρ : ℝ)
    (hσ : ∀ a, e (σ a) = z + (ρ : ℂ) *
      (((a.weights 1 : ℝ) : ℂ) + ((a.weights 2 : ℝ) : ℂ) * Complex.I)) :
    HasDerivAt (fun w : ℂ ↦ e (hga_triangleExtension σ w)) (ρ : ℂ) 0 := by
  have hd : HasDerivAt
      (fun w : ℂ ↦ z + (ρ : ℂ) * ((1 : ℂ) / 3 + (1 : ℂ) / 3 * Complex.I + w))
      (ρ : ℂ) 0 := by
    simpa only [mul_one, id_eq] using
      ((((hasDerivAt_id (0 : ℂ)).const_add
        ((1 : ℂ) / 3 + (1 : ℂ) / 3 * Complex.I)).const_mul (ρ : ℂ)).const_add z)
  exact hd.congr_of_eventuallyEq (hga_triangleExtension_eventually_affine σ e z ρ hσ)

#print axioms hga_triangleRetraction
#print axioms hga_triangleCoordinate
#print axioms hga_triangleRetraction_coordinate
#print axioms hga_continuous_triangleRetraction
#print axioms hga_triangleRetraction_barycentre_iff
#print axioms hga_triangleExtension
#print axioms hga_triangleExtension_coordinate
#print axioms hga_triangleExtension_barycentre_iff
#print axioms hga_triangleExtension_pairMap
#print axioms hga_triangleExtension_eventually_affine
#print axioms hga_triangleExtension_hasDerivAt
#print axioms hga_positive_barycentric_mass
#print axioms hga_normalize_barycentric
#print axioms hga_normalize_barycentric_nonnegative
#print axioms hga_normalize_barycentric_interior
#print axioms hga_continuous_normalize_barycentric

end HodgeLean.Foundations.Program
