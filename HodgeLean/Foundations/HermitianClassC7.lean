import HodgeLean.Foundations.HermitianClassC3
import HodgeLean.Foundations.HermitianClassC6

noncomputable section
namespace HodgeLean.Foundations.HermitianClass
open HermitianForm

/-- A regular indefinite Hermitian space of rank at least two contains a vector of length one.
Source: Serre, *A Course in Arithmetic*, Chapter IV, p. 43, Corollary 2. -/
theorem hermClass_represents_one (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [FiniteDimensional ℚ W] [FiniteDimensional (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate)
    (hrank : 2 ≤ Module.finrank (QuadraticAlgebra ℚ (-3) 0) W)
    (hp : ∃ x, 0 < traceQuad W h x) (hm : ∃ x, traceQuad W h x < 0) :
    ∃ x, h x x = 1 := by
  have htrace := hermClass_trace_regular W h hh hn
  have hassoc : (traceQuad W h).associated.SeparatingLeft := by
    have heq : (traceQuad W h).associated = traceBilin W h :=
      QuadraticMap.associated_left_inverse ℚ htrace.1.eq
    rw [heq]
    exact htrace.2.1
  have hdim : 4 ≤ Module.finrank ℚ W := by
    rw [← Module.finrank_mul_finrank ℚ (QuadraticAlgebra ℚ (-3) 0) W,
      QuadraticAlgebra.finrank_eq_two]
    omega
  obtain ⟨x, hx⟩ := quadratic_represents_nonzero W (traceQuad W h) hassoc hdim hp hm 2
    (by norm_num)
  refine ⟨x, ?_⟩
  have hfixed : h x x = algebraMap ℚ _ (h x x).re :=
    QuadraticAlgebraAux.star_eq_self_iff.1 (hh.eq x x)
  change 2 * (h x x).re = 2 at hx
  have hre : (h x x).re = 1 := by linarith
  rw [hfixed, hre]
  simp

#print axioms hermClass_represents_one

/-- A regular indefinite Hermitian plane has diagonal coordinates with first entry one.
Source: orthogonal splitting of a represented regular line. -/
theorem hermClass_binary_coordinates (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [FiniteDimensional ℚ W] [FiniteDimensional (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate)
    (hrank : Module.finrank (QuadraticAlgebra ℚ (-3) 0) W = 2)
    (hp : ∃ x, 0 < traceQuad W h x) (hm : ∃ x, traceQuad W h x < 0) :
    ∃ c : ℚ, c ≠ 0 ∧ ∃ e : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (QuadraticAlgebra ℚ (-3) 0 × QuadraticAlgebra ℚ (-3) 0),
      ∀ y z, h y z = star (e y).1 * (e z).1 +
        star (e y).2 * algebraMap ℚ _ c * (e z).2 := by
  let K := QuadraticAlgebra ℚ (-3) 0
  obtain ⟨x, hxx⟩ := hermClass_represents_one W h hh hn (hrank ▸ le_rfl) hp hm
  obtain ⟨V, e₀, hnV, hex, he₀⟩ :=
    hermClass_line_decomposition W h hh hn x (by rw [hxx]; norm_num)
  have hdimV : Module.finrank K V = 1 := by
    have hd : 2 = 1 + Module.finrank K V := by
      calc
        2 = Module.finrank K W := hrank.symm
        _ = Module.finrank K (K × V) := LinearEquiv.finrank_eq e₀
        _ = 1 + Module.finrank K V := by
          rw [Module.finrank_prod, Module.finrank_self]
    omega
  let ef : Fin (Module.finrank K V) ≃ Fin 1 := finCongr hdimV
  let eV : V ≃ₗ[K] K := (Module.finBasis K V).equivFun |>.trans
    ((LinearEquiv.piCongrLeft' K (fun _ : Fin (Module.finrank K V) ↦ K) ef).trans
      (LinearEquiv.funUnique (Fin 1) K K))
  let v : V := eV.symm 1
  let hV := h.domRestrict₁₂ V V
  let c : ℚ := (hV v v).re
  have hfixed : hV v v = algebraMap ℚ K c := by
    exact QuadraticAlgebraAux.star_eq_self_iff.1 ((hh.domRestrict V).eq v v)
  have hv0 : v ≠ 0 := by
    intro hv
    have := congrArg eV hv
    simpa [v] using this
  have hc0 : c ≠ 0 := by
    intro hc
    have hvv : hV v v = 0 := by rw [hfixed, hc]; simp
    apply hv0
    apply hnV.1 v
    intro y
    rw [show y = (eV y) • v by
      apply eV.injective
      simp [v]]
    change hV v ((eV y) • v) = 0
    simp [hvv]
  let ep := (LinearEquiv.refl K K).prodCongr eV
  let e := e₀.trans ep
  refine ⟨c, hc0, e, fun y z ↦ ?_⟩
  rw [he₀ y z, hxx]
  simp only [mul_one]
  have hy : (e₀ y).2 = (eV (e₀ y).2) • v := by
    apply eV.injective
    simp [v]
  have hz : (e₀ z).2 = (eV (e₀ z).2) • v := by
    apply eV.injective
    simp [v]
  change star (e₀ y).1 * (e₀ z).1 + hV (e₀ y).2 (e₀ z).2 = _
  rw [hy, hz]
  simp [hfixed, e, ep]
  ac_rfl

#print axioms hermClass_binary_coordinates

/-- A diagonal Hermitian plane with determinant class minus two can be rescaled to
coefficients one and minus two.
Source: the determinant quotient by the norm subgroup. -/
theorem hermClass_rescale_binary (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] (c : ℚ) (hc : c ≠ 0)
    (e : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
      (QuadraticAlgebra ℚ (-3) 0 × QuadraticAlgebra ℚ (-3) 0))
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0)
    (he : ∀ y z, h y z = star (e y).1 * (e z).1 +
      star (e y).2 * algebraMap ℚ _ c * (e z).2)
    (hclass :
      ((Units.mk0 c hc : ℚˣ) : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) =
      ((Units.mk0 (-2 : ℚ) (by norm_num) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0))) :
    ∃ e' : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (QuadraticAlgebra ℚ (-3) 0 × QuadraticAlgebra ℚ (-3) 0),
      ∀ y z, h y z = star (e' y).1 * (e' z).1 -
        2 * star (e' y).2 * (e' z).2 := by
  let K := QuadraticAlgebra ℚ (-3) 0
  let uc : ℚˣ := Units.mk0 c hc
  let un : ℚˣ := Units.mk0 (-2 : ℚ) (by norm_num)
  have hmem : uc / un ∈ normSubgroup K := by
    exact QuotientGroup.eq_iff_div_mem.mp hclass
  obtain ⟨z, hz⟩ := mem_normSubgroup_iff.mp hmem
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero, QuadraticAlgebra.norm_zero] at hz
    have hunit : ((uc / un : ℚˣ) : ℚ) ≠ 0 := Units.ne_zero _
    exact hunit hz.symm
  let ez : K ≃ₗ[K] K :=
    { toFun := fun t ↦ z * t
      invFun := fun t ↦ z⁻¹ * t
      left_inv := fun t ↦ by simp [hz0]
      right_inv := fun t ↦ by simp [hz0]
      map_add' := fun x y ↦ by ring
      map_smul' := fun r x ↦ by change z * (r * x) = r * (z * x); ring }
  let ep := (LinearEquiv.refl K K).prodCongr ez
  let e' := e.trans ep
  refine ⟨e', fun y w ↦ ?_⟩
  rw [he y w]
  have hnorm : algebraMap ℚ K c = -2 * algebraMap ℚ K (QuadraticAlgebra.norm z) := by
    have hrat : c = -2 * QuadraticAlgebra.norm z := by
      rw [hz]
      change c = -2 * (c / -2)
      ring
    calc
      algebraMap ℚ K c = algebraMap ℚ K (-2 * QuadraticAlgebra.norm z) :=
        congrArg (algebraMap ℚ K) hrat
      _ = -2 * algebraMap ℚ K (QuadraticAlgebra.norm z) := by
        simp only [map_neg, map_mul, map_ofNat]
  simp [e', ep, ez]
  change star (e y).1 * (e w).1 + star (e y).2 * algebraMap ℚ K c * (e w).2 = _
  rw [hnorm, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  ring

#print axioms hermClass_rescale_binary

/-- In binary coordinates with first coefficient one, the second coefficient represents
the determinant class.
Source: the diagonal Gram determinant formula. -/
theorem hermClass_binary_coefficient_class (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W]
    [FiniteDimensional (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate)
    (c : ℚ) (hc : c ≠ 0)
    (e : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
      (QuadraticAlgebra ℚ (-3) 0 × QuadraticAlgebra ℚ (-3) 0))
    (he : ∀ y z, h y z = star (e y).1 * (e z).1 +
      star (e y).2 * algebraMap ℚ _ c * (e z).2)
    (hdet : detClass h hh hn =
      ((Units.mk0 (-2 : ℚ) (by norm_num) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0))) :
    ((Units.mk0 c hc : ℚˣ) : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) =
      ((Units.mk0 (-2 : ℚ) (by norm_num) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
  let K := QuadraticAlgebra ℚ (-3) 0
  let d : Fin 2 → ℚ := ![1, c]
  let D := diagForm (a := (-3 : ℚ)) (b := 0) d
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    fin_cases i <;> simp [d, hc]
  let ep := (LinearEquiv.finTwoArrow K K).symm
  let eD := e.trans ep
  have heD : ∀ y z, D (eD y) (eD z) = h y z := by
    intro y z
    rw [he y z]
    simp [D, d, eD, ep, diagForm_apply, LinearEquiv.finTwoArrow]
  have hchange := detClass_eq_of_equiv W (Fin 2 → K) h D hh hn
    (diagForm_isSymm d) (diagForm_nondegenerate hd) eD heD
  calc
    ((Units.mk0 c hc : ℚˣ) : ℚˣ ⧸ normSubgroup K) =
        detClass D (diagForm_isSymm d) (diagForm_nondegenerate hd) := by
      rw [detClass_diagForm hd]
      congr 1
      apply Units.ext
      simp [d]
    _ = detClass h hh hn := hchange.symm
    _ = _ := hdet

#print axioms hermClass_binary_coefficient_class

/-- Three successive binary coordinate systems assemble into a six-entry diagonal system.
Source: associativity of orthogonal direct sums. -/
theorem hermClass_assemble_six_coordinates (W A B : Type*)
    [AddCommGroup W] [AddCommGroup A] [AddCommGroup B]
    [Module (QuadraticAlgebra ℚ (-3) 0) W]
    [Module (QuadraticAlgebra ℚ (-3) 0) A]
    [Module (QuadraticAlgebra ℚ (-3) 0) B]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0)
    (hA : A →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] A →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0)
    (hB : B →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] B →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0)
    (c : ℚ)
    (e₁ : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
      (QuadraticAlgebra ℚ (-3) 0 × QuadraticAlgebra ℚ (-3) 0 × A))
    (e₂ : A ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
      (QuadraticAlgebra ℚ (-3) 0 × QuadraticAlgebra ℚ (-3) 0 × B))
    (e₃ : B ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
      (QuadraticAlgebra ℚ (-3) 0 × QuadraticAlgebra ℚ (-3) 0))
    (he₁ : ∀ x y, h x y = star (e₁ x).1 * (e₁ y).1 -
      star (e₁ x).2.1 * (e₁ y).2.1 + hA (e₁ x).2.2 (e₁ y).2.2)
    (he₂ : ∀ x y, hA x y = star (e₂ x).1 * (e₂ y).1 -
      star (e₂ x).2.1 * (e₂ y).2.1 + hB (e₂ x).2.2 (e₂ y).2.2)
    (he₃ : ∀ x y, hB x y = star (e₃ x).1 * (e₃ y).1 +
      star (e₃ x).2 * algebraMap ℚ _ c * (e₃ y).2) :
    ∃ e : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (Fin 6 → QuadraticAlgebra ℚ (-3) 0),
      ∀ x y, diagForm ![1, -1, 1, -1, 1, c] (e x) (e y) = h x y := by
  let K := QuadraticAlgebra ℚ (-3) 0
  let e : W ≃ₗ[K] (Fin 6 → K) :=
    { toFun := fun x ↦
        let p := e₁ x
        let q := e₂ p.2.2
        let r := e₃ q.2.2
        ![p.1, p.2.1, q.1, q.2.1, r.1, r.2]
      invFun := fun f ↦ e₁.symm (f 0, f 1, e₂.symm (f 2, f 3, e₃.symm (f 4, f 5)))
      left_inv := fun x ↦ by simp
      right_inv := fun f ↦ by
        funext i
        fin_cases i <;> simp
      map_add' := fun x y ↦ by
        funext i
        fin_cases i <;> simp
      map_smul' := fun r x ↦ by
        funext i
        fin_cases i <;> simp }
  refine ⟨e, fun x y ↦ ?_⟩
  rw [he₁ x y, he₂ (e₁ x).2.2 (e₁ y).2.2,
    he₃ (e₂ (e₁ x).2.2).2.2 (e₂ (e₁ y).2.2).2.2]
  simp [e, diagForm_apply, Fin.sum_univ_succ]
  ring

#print axioms hermClass_assemble_six_coordinates

end HodgeLean.Foundations.HermitianClass
