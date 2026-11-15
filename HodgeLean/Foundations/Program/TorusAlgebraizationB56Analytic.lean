import HodgeLean.Foundations.Program.TorusAlgebraizationB56Evaluate

/-! # Regular functions along the theta map are holomorphic

Let `P z` be the complex point of the theta Proj given by evaluating theta functions at `z`.
Near any `z₀`, a regular function `s` on a Zariski open `W ∋ P z₀` is, along `P`, a quotient of
theta functions: choose `t` of degree one with `t(z₀) ≠ 0`, a principal open of the affine
`D₊(t)` around `P z₀` inside `W`, and write `s` there as `a / gᵏ`; each of `a`, `g` is a fraction
`b / tⁿ`. Hence `P⁻¹(W)` is open, `z ↦ s(P z)` is holomorphic on it, and `P` is continuous.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

variable {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
  {F : Submodule ℂ (ℂ ⊗[ℤ] Λ)} {hF : b2_IsWeightOne Λ F} {Q : LinearMap.BilinForm ℤ Λ}

/-- Evaluation of an element of the section ring is holomorphic in the cover coordinate. -/
theorem b56_differentiable_eval (a : b5_S Λ F hF Q) :
    Differentiable ℂ (fun z ↦ b5_eval Λ F hF Q z a) := by
  induction a using DirectSum.induction_on with
  | zero => simpa using differentiable_const (0 : ℂ)
  | of n σ =>
    have h (z : b5_V Λ F) : b5_eval Λ F hF Q z (DirectSum.of _ n σ) = σ.val z := by
      simp [b5_eval]
    simp only [h]
    exact σ.property.1
  | add a b ha hb =>
    simp only [map_add]
    exact ha.add hb

/-- Evaluation of an element of the section ring is continuous in the cover coordinate. -/
theorem b56_continuous_eval (a : b5_S Λ F hF Q) :
    Continuous (fun z ↦ b5_eval Λ F hF Q z a) :=
  (b56_differentiable_eval a).continuous

variable (hirr : ∀ z, (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q z) = ⊤)
  (P : b5_V Λ F → ComplexPoint (b5_model Λ F hF Q))
  (hP : ∀ z, (P z).left =
    Proj.fromOfGlobalSections (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q z) (hirr z))
include hP

/-- Along the theta map, every regular function on `D₊(t)` is a quotient `a / tⁿ` of elements of
the section ring, wherever `t ≠ 0`.
Source: Hartshorne, *Algebraic Geometry*, Proposition II.2.5(b). -/
theorem b56_evaluate_basicOpen_eq_div {t : b5_S Λ F hF Q} {m : ℕ} (hm : 0 < m)
    (ht : t ∈ b5_grade Λ F hF Q m)
    (σ : Γ((b5_model Λ F hF Q).left, Proj.basicOpen (b5_grade Λ F hF Q) t)) :
    ∃ (n : ℕ) (a : b5_S Λ F hF Q), ∀ z, b5_eval Λ F hF Q z t ≠ 0 →
      Point.evaluate (Proj.basicOpen (b5_grade Λ F hF Q) t) σ (P z) =
        b5_eval Λ F hF Q z a / b5_eval Λ F hF Q z t ^ n := by
  let e := Proj.basicOpenIsoAway (b5_grade Λ F hF Q) t ht hm
  obtain ⟨n, a, ha, hx⟩ := HomogeneousLocalization.Away.mk_surjective (b5_grade Λ F hF Q) ht
    (e.inv σ)
  refine ⟨n, a, fun z htz ↦ ?_⟩
  have hσ : σ = Proj.awayToSection (b5_grade Λ F hF Q) t (e.inv σ) := by
    change σ = e.hom (e.inv σ)
    exact (e.inv_hom_id_apply σ).symm
  rw [hσ, b56_evaluate_awayToSection z (hirr z) (P z) (hP z) htz hm ht, ← hx]
  rw [eq_div_iff (pow_ne_zero _ htz), mul_comm]
  exact b56_awayEval_mk Λ F hF Q z htz ht n a ha

/-- Locally along the theta map, a regular function is holomorphic.
Source: Hartshorne, *Algebraic Geometry*, Proposition II.2.5(b); Mumford, *Abelian Varieties*,
§3 (theta functions give holomorphic projective coordinates). -/
theorem b56_evaluate_local
    (hbpf : ∀ z, ∃ t ∈ b5_grade Λ F hF Q 1, b5_eval Λ F hF Q z t ≠ 0)
    (W : (b5_model Λ F hF Q).left.Opens) (s : Γ((b5_model Λ F hF Q).left, W))
    (z₀ : b5_V Λ F) (hz₀ : P z₀ ∈ Point.overOpen W) :
    ∃ N : Set (b5_V Λ F), IsOpen N ∧ z₀ ∈ N ∧ (∀ z ∈ N, P z ∈ Point.overOpen W) ∧
      DifferentiableOn ℂ (fun z ↦ Point.evaluate W s (P z)) N := by
  obtain ⟨t, ht, htz₀⟩ := hbpf z₀
  let U : (b5_model Λ F hF Q).left.Opens := Proj.basicOpen (b5_grade Λ F hF Q) t
  have hU : IsAffineOpen U := Proj.isAffineOpen_basicOpen (b5_grade Λ F hF Q) t ht one_pos
  have hxU : P z₀ ∈ Point.overOpen U := b56_mem_basicOpen z₀ (hirr z₀) (P z₀) (hP z₀) htz₀
    one_pos ht
  obtain ⟨g, hgle, hxg⟩ := hU.exists_basicOpen_le (V := U ⊓ W)
    ⟨(P z₀).underlying, hxU, hz₀⟩ hxU
  have hgW : (b5_model Λ F hF Q).left.basicOpen g ≤ W := hgle.trans inf_le_right
  let s' := (b5_model Λ F hF Q).left.presheaf.map (homOfLE hgW).op s
  obtain ⟨k, a, hka⟩ := Point.exists_evaluate_basicOpen_eq_div hU g s'
  obtain ⟨ng, bg, hg⟩ := b56_evaluate_basicOpen_eq_div hirr P hP one_pos ht g
  obtain ⟨na, ba, hba⟩ := b56_evaluate_basicOpen_eq_div hirr P hP one_pos ht a
  let N : Set (b5_V Λ F) :=
    {z | b5_eval Λ F hF Q z t ≠ 0} ∩ {z | b5_eval Λ F hF Q z bg ≠ 0}
  have hNopen : IsOpen N :=
    (isOpen_ne_fun (b56_continuous_eval t) continuous_const).inter
      (isOpen_ne_fun (b56_continuous_eval bg) continuous_const)
  have hmemU (z : b5_V Λ F) (hz : z ∈ N) : P z ∈ Point.overOpen U :=
    b56_mem_basicOpen z (hirr z) (P z) (hP z) hz.1 one_pos ht
  have hmemg (z : b5_V Λ F) (hz : z ∈ N) :
      P z ∈ Point.overOpen ((b5_model Λ F hF Q).left.basicOpen g) := by
    rw [Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero g (P z) (hmemU z hz), hg z hz.1]
    exact div_ne_zero hz.2 (pow_ne_zero _ hz.1)
  have hz₀N : z₀ ∈ N := by
    refine ⟨htz₀, fun h ↦ ?_⟩
    have hne := (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero g (P z₀) hxU).mp hxg
    rw [hg z₀ htz₀, h, zero_div] at hne
    exact hne rfl
  have hformula (z : b5_V Λ F) (hz : z ∈ N) : Point.evaluate W s (P z) =
      (b5_eval Λ F hF Q z ba / b5_eval Λ F hF Q z t ^ na) /
        (b5_eval Λ F hF Q z bg / b5_eval Λ F hF Q z t ^ ng) ^ k := by
    rw [Point.evaluate_res hgW s (P z) (hmemg z hz), hka (P z) (hmemg z hz), hba z hz.1,
      hg z hz.1]
  refine ⟨N, hNopen, hz₀N, fun z hz ↦ hgW (hmemg z hz), ?_⟩
  have hd : DifferentiableOn ℂ (fun z ↦
      (b5_eval Λ F hF Q z ba / b5_eval Λ F hF Q z t ^ na) /
        (b5_eval Λ F hF Q z bg / b5_eval Λ F hF Q z t ^ ng) ^ k) N := by
    intro z hz
    have ht' := pow_ne_zero na hz.1
    have ht'' := pow_ne_zero ng hz.1
    have h1 := b56_differentiable_eval (hF := hF) (Q := Q) ba
    have h2 := b56_differentiable_eval (hF := hF) (Q := Q) t
    have h3 := b56_differentiable_eval (hF := hF) (Q := Q) bg
    have h5 := pow_ne_zero k (div_ne_zero hz.2 ht'')
    exact DifferentiableAt.differentiableWithinAt (by fun_prop (disch := assumption))
  exact hd.congr hformula

/-- The preimage of a Zariski open along the theta map is open. -/
theorem b56_isOpen_preimage
    (hbpf : ∀ z, ∃ t ∈ b5_grade Λ F hF Q 1, b5_eval Λ F hF Q z t ≠ 0)
    (W : (b5_model Λ F hF Q).left.Opens) :
    IsOpen (P ⁻¹' Point.overOpen W) := by
  rw [isOpen_iff_forall_mem_open]
  intro z₀ hz₀
  obtain ⟨N, hN, hz₀N, hNW, -⟩ := b56_evaluate_local hirr P hP hbpf W 0 z₀ hz₀
  exact ⟨N, hNW, hN, hz₀N⟩

/-- Along the theta map, a regular function is holomorphic on the preimage of its domain. -/
theorem b56_differentiableOn_evaluate
    (hbpf : ∀ z, ∃ t ∈ b5_grade Λ F hF Q 1, b5_eval Λ F hF Q z t ≠ 0)
    (W : (b5_model Λ F hF Q).left.Opens) (s : Γ((b5_model Λ F hF Q).left, W)) :
    DifferentiableOn ℂ (fun z ↦ Point.evaluate W s (P z)) (P ⁻¹' Point.overOpen W) := by
  intro z₀ hz₀
  obtain ⟨N, hN, hz₀N, -, hd⟩ := b56_evaluate_local hirr P hP hbpf W s z₀ hz₀
  exact ((hd z₀ hz₀N).differentiableAt (hN.mem_nhds hz₀N)).differentiableWithinAt

/-- The theta map is continuous for the analytic topology.
Source: HodgeConjecture `Point.continuous_iff_analyticSubbasis`. -/
theorem b56_continuous
    (hbpf : ∀ z, ∃ t ∈ b5_grade Λ F hF Q 1, b5_eval Λ F hF Q z t ≠ 0) :
    Continuous P := by
  rw [Point.continuous_iff_analyticSubbasis]
  rintro _ ⟨W, s, V, hV, rfl⟩
  rw [Set.preimage_inter]
  exact (b56_differentiableOn_evaluate hirr P hP hbpf W s).continuousOn.isOpen_inter_preimage
    (b56_isOpen_preimage hirr P hP hbpf W) hV

end HodgeLean.Foundations.Program
