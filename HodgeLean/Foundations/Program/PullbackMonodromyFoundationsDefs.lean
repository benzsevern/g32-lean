import HodgeLean.Foundations.Program.PullbackMonodromyDefs

/-! # Pulled-back coefficients, punctured discs on the sphere and peripheral loops

The coefficient pullback, the sphere discs about finite points and about infinity, the
inclusion of a punctured open set and its peripheral loop classes.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric
namespace HodgeLean.Foundations.Program

/-- The coefficient of the pulled-back system: `φ'(z) • A(φ z)`.
Source: Ilyashenko–Yakovenko, Lectures on Analytic Differential Equations, §15, change of the independent variable. -/
def b65t_pull (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (φ : ℂ → ℂ) (A : ℂ → E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  deriv φ z • A (φ z)

example (A : ℂ → ℂ →L[ℂ] ℂ) (z : ℂ) : b65t_pull ℂ id A z = A z := by
  simp [b65t_pull]

/-- A nonconstant map and a nonzero rank-one coefficient give a nonzero pullback value. -/
example : b65t_pull ℂ (fun z ↦ z ^ 2) (fun z ↦ z⁻¹ • (1 : ℂ →L[ℂ] ℂ)) 1 ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : ℂ →L[ℂ] ℂ ↦ f 1) h
  simp [b65t_pull] at h1

/-- Open disc of radius `r` about a point of the sphere, in the chart at infinity for `∞`.
Source: OnePoint ℂ as the Riemann sphere; the charts z and 1/z. -/
def b65t_disc (p : OnePoint ℂ) (r : ℝ) : Set (OnePoint ℂ) :=
  p.elim (insert OnePoint.infty (((↑) : ℂ → OnePoint ℂ) '' {z : ℂ | r⁻¹ < ‖z‖}))
    (fun a ↦ ((↑) : ℂ → OnePoint ℂ) '' ball a r)

example : (OnePoint.infty : OnePoint ℂ) ∈ b65t_disc OnePoint.infty 1 := by
  simp [b65t_disc]

example : ((0 : ℂ) : OnePoint ℂ) ∈ b65t_disc ((0 : ℂ) : OnePoint ℂ) 1 :=
  ⟨0, by simp, rfl⟩

example : ((1 : ℂ) : OnePoint ℂ) ∉ b65t_disc ((0 : ℂ) : OnePoint ℂ) 1 := by
  rintro ⟨z, hz, he⟩
  have : z = 1 := OnePoint.coe_injective he
  subst this
  simp at hz

/-- Inclusion of an open set of the sphere with finitely many points removed.
Source: Set.inclusion and continuous_inclusion. -/
def b65t_fill (X : Set (OnePoint ℂ)) (F : Finset (OnePoint ℂ)) :
    C(↥(X \ (F : Set (OnePoint ℂ))), ↥X) :=
  ⟨Set.inclusion sdiff_subset, continuous_inclusion sdiff_subset⟩

example (X : Set (OnePoint ℂ)) (F : Finset (OnePoint ℂ)) (x : ↥(X \ (F : Set (OnePoint ℂ)))) :
    (b65t_fill X F x : OnePoint ℂ) = x := rfl

/-- Classes of loops that run along a path, around a loop inside a disc of `X` meeting `F`
only in its centre, and back. Their normal closure is the kernel of filling in `F`.
Source: Hatcher, Algebraic Topology, §1.2, Theorem 1.20 (van Kampen) and Proposition 1.26. -/
def b65t_peripheral (X : Set (OnePoint ℂ)) (F : Finset (OnePoint ℂ))
    (x : ↥(X \ (F : Set (OnePoint ℂ)))) :
    Set (FundamentalGroup ↥(X \ (F : Set (OnePoint ℂ))) x) :=
  {c | ∃ p ∈ F, ∃ r : ℝ, 0 < r ∧ b65t_disc p r ⊆ X ∧
    (∀ q ∈ F, q ∈ b65t_disc p r → q = p) ∧
    ∃ y : ↥(X \ (F : Set (OnePoint ℂ))), ∃ δ : Path x y, ∃ γ : Path y y,
      (∀ t, ((γ t : ↥(X \ (F : Set (OnePoint ℂ)))) : OnePoint ℂ) ∈ b65t_disc p r) ∧
      c = FundamentalGroup.fromPath ⟦(δ.trans γ).trans δ.symm⟧}

/-- In the plane `{∞}ᶜ` of the sphere with `F = {0}` and base point `1`, the positive unit circle
`t ↦ exp(2πit)` gives a peripheral class about zero, and that class is not the identity in the
fundamental group of the punctured plane: its lift through the covering `exp : ℂ → ℂ \ {0}` from `0`
ends at `2πi`, while the constant loop lifts to the constant path at `0`. -/
example :
    let X : Set (OnePoint ℂ) := {OnePoint.infty}ᶜ
    let F : Finset (OnePoint ℂ) := {((0 : ℂ) : OnePoint ℂ)}
    let f : {z : ℂ // z ≠ 0} → ↥(X \ (F : Set (OnePoint ℂ))) :=
      fun z ↦ ⟨(z : ℂ), by simp [X, F, z.2]⟩
    let x : ↥(X \ (F : Set (OnePoint ℂ))) := f ⟨1, one_ne_zero⟩
    let c : Path (⟨1, one_ne_zero⟩ : {z : ℂ // z ≠ 0}) ⟨1, one_ne_zero⟩ :=
      { toFun := fun t ↦ ⟨Complex.exp (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)),
          Complex.exp_ne_zero _⟩
        continuous_toFun := by fun_prop
        source' := by ext; simp
        target' := by ext; simp }
    let γ : Path x x := c.map (f := f) (by fun_prop)
    FundamentalGroup.fromPath ⟦((Path.refl x).trans γ).trans (Path.refl x).symm⟧ ∈
        b65t_peripheral X F x ∧
      FundamentalGroup.fromPath ⟦((Path.refl x).trans γ).trans (Path.refl x).symm⟧ ≠ 1 := by
  intro X F f x c γ
  have hf : Topology.IsEmbedding f :=
    (Topology.IsEmbedding.subtypeVal.of_comp_iff (f := f)).mp
      ((OnePoint.isOpenEmbedding_coe.isEmbedding).comp Topology.IsEmbedding.subtypeVal)
  have hs : Function.Surjective f := by
    rintro ⟨w, hw, hw0⟩
    obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hw
    exact ⟨⟨z, fun h ↦ hw0 (by simp [F, h])⟩, rfl⟩
  have cov := Complex.isCoveringMap_exp.homeomorph_comp (hf.toHomeomorphOfSurjective hs)
  refine ⟨⟨_, Finset.mem_singleton_self _, 2, by norm_num, ?_, ?_, x, Path.refl x, γ, ?_, rfl⟩,
    fun h ↦ ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    simp [X]
  · intro q hq _
    simpa [F] using hq
  · intro t
    refine ⟨Complex.exp (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)), ?_, rfl⟩
    rw [mem_ball_zero_iff, show 2 * Real.pi * Complex.I * ((t : ℝ) : ℂ) =
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hh : (((Path.refl x).trans γ).trans (Path.refl x).symm).Homotopic (Path.refl x) :=
    Quotient.exact (congrArg FundamentalGroup.toPath h)
  have hγ : γ.Homotopic (Path.refl x) :=
    ((Path.Homotopic.trans_refl _).trans (Path.Homotopic.refl_trans γ)).symm.trans hh
  have hΓ : (hf.toHomeomorphOfSurjective hs ∘ fun z : ℂ ↦
      (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) ∘
      (fun t : unitInterval ↦ 2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)) = γ := by
    rfl
  have h0 : γ.toContinuousMap 0 = (hf.toHomeomorphOfSurjective hs ∘ fun z : ℂ ↦
      (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) 0 := by
    simp [γ, x, f]
  have h1 : (Path.refl x).toContinuousMap 0 = (hf.toHomeomorphOfSurjective hs ∘ fun z : ℂ ↦
      (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) 0 := by
    simp [x, f]
  have key := cov.liftPath_apply_one_eq_of_homotopicRel hγ 0 h0 h1
  rw [← (cov.eq_liftPath_iff' h1 (Γ := ContinuousMap.const _ (0 : ℂ))).mpr
    ⟨funext fun _ ↦ h1.symm, rfl⟩] at key
  rw [show cov.liftPath γ.toContinuousMap 0 h0 =
      ⟨fun t : unitInterval ↦ 2 * Real.pi * Complex.I * ((t : ℝ) : ℂ), by fun_prop⟩ from
    ((cov.eq_liftPath_iff' ..).mpr ⟨hΓ, by simp⟩).symm] at key
  simp [Real.pi_ne_zero] at key

/-- A two-sheeted covering map with two distinct points in one fibre. -/
example :
    IsCoveringMap ((2 : ℕ) • · : AddCircle (1 : ℝ) → AddCircle (1 : ℝ)) ∧
      ((2 : ℕ) • ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = 0) ∧
      ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
  refine ⟨(AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero (1 : ℝ) 2).isCoveringMap,
    ?_, ?_⟩
  · rw [← AddCircle.coe_nsmul]
    norm_num
  · rw [Ne, AddCircle.coe_eq_zero_iff]
    rintro ⟨n, hn⟩
    have h : (n : ℝ) * 2 = 1 := by norm_num at hn; linarith
    have h' : n * 2 = 1 := by exact_mod_cast h
    omega

example : 0 < Module.finrank ℂ (Fin 4 → ℂ) := by simp

/-- The first reflection has a nonidentity matrix. -/
example : b4b_toMatrix (b4b_generators 0) ≠ 1 := by
  intro h
  have h1 : b4b_generators 0 = 1 :=
    Subtype.val_injective (h.trans (map_one b4b_toMatrix).symm)
  have ho := b63_root_order (0 : Fin 13)
  change orderOf (b4b_generators 0) = _ at ho
  rw [h1, orderOf_one] at ho
  norm_num at ho

end HodgeLean.Foundations.Program
