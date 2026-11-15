import HodgeLean.Adapters.IntersectionProductMovingProjCharts
import HodgeLean.Adapters.IntersectionProductMovingHomog

/-! # Charts on the product with the projective line

For a scheme `X` with projective `Spec`-charts `κ_j : Spec T_j ⟶ X` (dehomogenizations
`θ_j : ℂ[x] → T_j`), the fibre product `X × ℙ¹_ℤ` over the integers (the upstream
`ProjectiveSpace (Fin 2) X`) has, over the affine line `s₀ ≠ 0`, the product charts
`Spec (T_j ⊗[ℤ] ℤ[t]) ⟶ X × D₊(s₀)`, `t = s₁/s₀`, with dehomogenizations
`ℂ[t][x] → T_j ⊗[ℤ] ℤ[t]`, `x_k ↦ θ_j(x_k) ⊗ 1`, `t ↦ 1 ⊗ t`. They satisfy the chart axioms
relative to `X × ℙ¹_ℤ`, so the points of `X × 𝔸¹` are the relevant `x`-homogeneous primes of
`ℂ[t][x]` containing the ideal of `X`.

Source: Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 and Proposition 2.5.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations

namespace HodgeLean.Adapters

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The chart ring `ℤ[t] = ℤ[s₀, s₁]_(s₀)` of the affine line in `ℙ¹_ℤ`. -/
abbrev a3m_Away1 : Type := Away (UniversalGrading 1) (X 0 : UniversalRing 1)

/-- The coordinate `t = s₁/s₀`. -/
abbrev a3m_t₁ : a3m_Away1 := chartCoordinate 0 1

/-- The product `X × ℙ¹_ℤ` over the integers. -/
abbrev a3m_T (Xs : Scheme.{0}) : Scheme.{0} := pullback (terminal.from Xs) (terminal.from (g3c_P 1))

instance a3m_Away1_isDomain : IsDomain a3m_Away1 := by
  have : IsDomain (ULift.{0} ℤ) :=
    Function.Injective.isDomain (ULift.ringEquiv (R := ℤ)).toRingHom ULift.ringEquiv.injective
  have : IsDomain (Localization.Away (X 0 : UniversalRing 1)) :=
    IsLocalization.isDomain_localization
      (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero (R := ULift.{0} ℤ) (0 : Fin 2)))
  exact Function.Injective.isDomain (algebraMap a3m_Away1 (Localization.Away (X 0 : UniversalRing 1)))
    (fun a b h => HomogeneousLocalization.val_injective _ (by simpa using h))

/-- The generic point of the affine line `D₊(s₀)`. -/
def a3m_bot1 : Spec (.of a3m_Away1) := ⟨⊥, Ideal.isPrime_bot⟩

/-- The zero `t = 0` of the coordinate on `ℙ¹_ℤ`. -/
def a3m_Z0 : Set (g3c_P 1) := {c | ∃ q : Spec (.of a3m_Away1), g3c_chartι 1 0 q = c ∧ a3m_t₁ ∈ q.asIdeal}

/-- The point `t = 1` of `ℙ¹_ℤ`. -/
def a3m_Zinf : Set (g3c_P 1) :=
  {c | ∃ q : Spec (.of a3m_Away1), g3c_chartι 1 0 q = c ∧ a3m_t₁ - 1 ∈ q.asIdeal}

theorem a3m_homogeneousComponent_map {σ R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (G : MvPolynomial σ R) (e : ℕ) :
    homogeneousComponent e (MvPolynomial.map f G) = MvPolynomial.map f (homogeneousComponent e G) := by
  ext d
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

/-- `s₀ ↦ 1`, `s₁ ↦ X`, from `ℤ[s₀, s₁]` to `ℤ[X]`. -/
def a3m_ψZ : UniversalRing 1 →+* Polynomial ℤ :=
  eval₂Hom (Polynomial.C.comp ULift.ringEquiv.toRingHom) ![1, Polynomial.X]

/-- Evaluation at the coordinate `t`. -/
def a3m_evt : Polynomial ℤ →+* a3m_Away1 := Polynomial.eval₂RingHom (Int.castRingHom _) a3m_t₁

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem a3m_evt_ψZ : a3m_evt.comp a3m_ψZ =
    eval₂Hom ((fromZeroRingHom (UniversalGrading 1) (.powers (X 0))).comp
      (ProjectiveSpace.degreeZeroEquiv (Fin 2) (ULift.{0} ℤ)).symm.toRingHom)
      (chartCoordinate 0) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun k => ?_)
  · have h1 : ((a3m_evt.comp a3m_ψZ).comp MvPolynomial.C).comp
        (ULift.ringEquiv (R := ℤ)).symm.toRingHom =
        ((eval₂Hom ((fromZeroRingHom (UniversalGrading 1) (.powers (X 0))).comp
          (ProjectiveSpace.degreeZeroEquiv (Fin 2) (ULift.{0} ℤ)).symm.toRingHom)
          (chartCoordinate 0)).comp MvPolynomial.C).comp
            (ULift.ringEquiv (R := ℤ)).symm.toRingHom := RingHom.ext_int _ _
    have := congrArg (fun φ : ℤ →+* a3m_Away1 => φ c.down) h1
    exact this
  · fin_cases k
    · simp [a3m_evt, a3m_ψZ]
    · simp [a3m_evt, a3m_ψZ]

/-- `ℤ[t] → ℤ[s₀, s₁]_(s₀)`, `t ↦ s₁/s₀`, is injective: the chart ring of the affine line is the
polynomial ring in `t`. -/
theorem a3m_evt_injective : Function.Injective a3m_evt := by
  have hX0 : a3m_ψZ (X 0) = 1 := by
    simp only [a3m_ψZ, coe_eval₂Hom, eval₂_X]
    rfl
  have hu : IsUnit (a3m_ψZ (X 0)) := by rw [hX0]; exact isUnit_one
  let lift1 : Localization.Away (X 0 : UniversalRing 1) →+* Polynomial ℤ :=
    Localization.awayLift a3m_ψZ (X 0) hu
  set f₁ := (lift1.comp (algebraMap a3m_Away1 (Localization.Away (X 0 : UniversalRing 1)))).comp
      a3m_evt
  have hcomp : f₁ = RingHom.id _ := by
    refine Polynomial.ringHom_ext (fun n => ?_) ?_
    · exact congrArg (fun φ : ℤ →+* Polynomial ℤ => φ n)
        (RingHom.ext_int (f₁.comp Polynomial.C) ((RingHom.id _).comp Polynomial.C))
    · simp only [f₁, RingHom.comp_apply, RingHom.id_apply, a3m_evt, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, HomogeneousLocalization.algebraMap_apply]
      have hv : a3m_ψZ (X 0) * 1 = 1 := by rw [hX0, one_mul]
      rw [show (a3m_t₁).val = Localization.mk (X 1 : UniversalRing 1)
          (⟨X 0 ^ 1, 1, rfl⟩ : Submonoid.powers (X 0 : UniversalRing 1)) from rfl,
        show lift1 = Localization.awayLift a3m_ψZ (X 0) (isUnit_iff_exists_inv.mpr ⟨1, hv⟩)
          from rfl, Localization.awayLift_mk _ _ _ 1 hv 1]
      simp [a3m_ψZ]
  intro f g h
  have h2 : f₁ f = f₁ g := by simp only [f₁, RingHom.comp_apply, h]
  rwa [hcomp] at h2


theorem a3m_evt_surjective : Function.Surjective a3m_evt := by
  intro a
  obtain ⟨P, rfl⟩ := a3m_awayCoord_surj 1 0 a
  exact ⟨a3m_ψZ P, by rw [← RingHom.comp_apply, a3m_evt_ψZ]⟩

/-- `ℤ[t] ≅ ℤ[s₀, s₁]_(s₀)` as `ℤ`-algebras. -/
def a3m_evtEquiv : Polynomial ℤ ≃ₐ[ℤ] a3m_Away1 :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective a3m_evt ⟨a3m_evt_injective, a3m_evt_surjective⟩)
    (fun n => by simp)

/-- `A[t] → A ⊗[ℤ] ℤ[t]`, `a ↦ a ⊗ 1`, `t ↦ 1 ⊗ t`, is injective. -/
theorem a3m_tensor_eval₂_injective (A : Type) [CommRing A] :
    Function.Injective (Polynomial.eval₂RingHom
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := a3m_Away1))
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) a3m_t₁)) := by
  set e := (polyEquivTensor ℤ A).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := ℤ) (A₁ := A)) a3m_evtEquiv)
  have : Polynomial.eval₂RingHom
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := a3m_Away1))
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) a3m_t₁) = e.toRingHom := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [e, a3m_evtEquiv]
    · simp [e, a3m_evtEquiv, a3m_evt]
  rw [this]
  exact e.injective

section LineCharts

variable {Xs : Scheme.{0}} {σ : Type} (CX : a3m_SpecCharts Xs σ ℂ)

/-- The chart ring `T_j ⊗[ℤ] ℤ[t]`. -/
abbrev a3m_TT (j : σ) : CommRingCat.{0} := .of (TensorProduct ℤ (CX.T j) a3m_Away1)

/-- The product chart `Spec (T_j ⊗[ℤ] ℤ[t]) ⟶ X × ℙ¹_ℤ`. -/
def a3m_Tκ (j : σ) : Spec (a3m_TT CX j) ⟶ a3m_T Xs :=
  a3m_prodChart (CX.κ j) (g3c_chartι 1 0)

instance (j : σ) : IsOpenImmersion (a3m_Tκ CX j) := a3m_prodChart_isOpenImmersion _ _

/-- The dehomogenization `ℂ[t][x] → T_j ⊗[ℤ] ℤ[t]`. -/
def a3m_Tθ (j : σ) : MvPolynomial σ (Polynomial ℂ) →+* a3m_TT CX j :=
  eval₂Hom (Polynomial.eval₂RingHom
      ((Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := CX.T j) (B := a3m_Away1)).comp
        ((CX.θ j).comp MvPolynomial.C))
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := CX.T j) a3m_t₁))
    (fun k => Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := CX.T j) (B := a3m_Away1)
      (CX.θ j (X k)))

theorem a3m_Tθ_X_self (j : σ) : a3m_Tθ CX j (X j) = 1 := by
  simp [a3m_Tθ, CX.θ_X_self]
  rfl

/-- Polynomials with constant coefficients dehomogenize through the chart of `X`. -/
theorem a3m_Tθ_map_C (j : σ) (G : MvPolynomial σ ℂ) :
    a3m_Tθ CX j (MvPolynomial.map Polynomial.C G) =
      Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := CX.T j) (B := a3m_Away1)
        (CX.θ j G) := by
  have : (a3m_Tθ CX j).comp (MvPolynomial.map Polynomial.C) =
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := CX.T j) (B := a3m_Away1)).comp
        (CX.θ j) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun k => ?_)
    · simp [a3m_Tθ]
    · simp [a3m_Tθ]
  exact congrArg (fun φ : MvPolynomial σ ℂ →+* a3m_TT CX j => φ G) this

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem a3m_Tθ_surj (j : σ) : Function.Surjective (a3m_Tθ CX j) := by
  set S := (a3m_Tθ CX j).range
  have hL : ∀ s : CX.T j, Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := CX.T j)
      (B := a3m_Away1) s ∈ S := by
    intro s
    obtain ⟨G, rfl⟩ := CX.θ_surj j s
    exact ⟨_, a3m_Tθ_map_C CX j G⟩
  have hcoord : ∀ k : Fin 2, Algebra.TensorProduct.includeRight (R := ℤ) (A := CX.T j)
      (chartCoordinate (0 : Fin 2) k) ∈ S := by
    intro k
    fin_cases k
    · simp only [Fin.zero_eta, chartCoordinate_self, map_one]
      exact S.one_mem
    · refine ⟨MvPolynomial.C Polynomial.X, ?_⟩
      simp [a3m_Tθ]
  have hR : ∀ P : UniversalRing 1, Algebra.TensorProduct.includeRight (R := ℤ) (A := CX.T j)
      (eval₂Hom ((fromZeroRingHom (UniversalGrading 1) (.powers (X 0))).comp
        (ProjectiveSpace.degreeZeroEquiv (Fin 2) (ULift.{0} ℤ)).symm.toRingHom)
        (chartCoordinate 0) P) ∈ S := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C c =>
      have hc : (MvPolynomial.C c : UniversalRing 1) = ((c.down : ℤ) : UniversalRing 1) := by
        obtain ⟨c⟩ := c
        rw [← map_intCast (MvPolynomial.C (σ := Fin 2) (R := ULift.{0} ℤ)) c]
        rfl
      rw [hc, map_intCast, map_intCast]
      exact intCast_mem S _
    | add P Q hP hQ =>
      simp only [coe_eval₂Hom, eval₂_add] at hP hQ ⊢
      rw [map_add]
      exact S.add_mem hP hQ
    | mul_X P k hP =>
      simp only [coe_eval₂Hom, eval₂_mul, eval₂_X] at hP ⊢
      rw [map_mul]
      exact S.mul_mem hP (hcoord k)
  intro t
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
  | tmul s a =>
    obtain ⟨P, rfl⟩ := a3m_awayCoord_surj 1 0 a
    have h1 := hL s
    have h2 := hR P
    have := S.mul_mem h1 h2
    change _ ∈ S
    simpa [Algebra.TensorProduct.tmul_mul_tmul] using this

theorem a3m_Tinter (j l : σ) (p : Spec (a3m_TT CX l)) :
    a3m_Tκ CX l p ∈ Set.range (a3m_Tκ CX j) ↔ a3m_Tθ CX l (X j) ∉ p.asIdeal := by
  have h := a3m_range_prodChart (CX.κ j) (g3c_chartι 1 0)
  have hfst : pullback.fst (terminal.from Xs) (terminal.from (g3c_P 1)) (a3m_Tκ CX l p) =
      CX.κ l (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := ℤ) (A := CX.T l) (B := a3m_Away1))) p) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    exact congrArg (fun f => f p) (a3m_prodChart_fst (CX.κ l) (g3c_chartι 1 0))
  have hsnd : pullback.snd (terminal.from Xs) (terminal.from (g3c_P 1)) (a3m_Tκ CX l p) ∈
      Set.range (g3c_chartι 1 0) := by
    rw [← Scheme.Hom.comp_apply]
    rw [show a3m_Tκ CX l ≫ pullback.snd (terminal.from Xs) (terminal.from (g3c_P 1)) = _ from
      a3m_prodChart_snd (CX.κ l) (g3c_chartι 1 0)]
    exact ⟨_, rfl⟩
  have hmem : a3m_Tκ CX l p ∈ Set.range (a3m_Tκ CX j) ↔
      pullback.fst (terminal.from Xs) (terminal.from (g3c_P 1)) (a3m_Tκ CX l p) ∈
        Set.range (CX.κ j) := by
    change a3m_Tκ CX l p ∈ Set.range (a3m_prodChart (CX.κ j) (g3c_chartι 1 0)) ↔ _
    rw [h]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', hsnd⟩⟩
  rw [hmem, hfst, CX.inter]
  change CX.θ l (X j) ∉ Ideal.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ)
    (A := CX.T l) (B := a3m_Away1)) p.asIdeal ↔ _
  rw [Ideal.mem_comap]
  simp [a3m_Tθ]

set_option maxHeartbeats 400000 in
theorem a3m_Thov [Fintype σ]
    (hovX : ∀ (j l : σ) (F : MvPolynomial σ ℂ) (e : ℕ), F.IsHomogeneous e →
      (pullback.snd (CX.κ j) (CX.κ l)).appTop ((Scheme.ΓSpecIso _).inv (CX.θ l F)) =
        (pullback.snd (CX.κ j) (CX.κ l)).appTop ((Scheme.ΓSpecIso _).inv (CX.θ l (X j))) ^ e *
          (pullback.fst (CX.κ j) (CX.κ l)).appTop ((Scheme.ΓSpecIso _).inv (CX.θ j F)))
    (j l : σ) (F : MvPolynomial σ (Polynomial ℂ)) (e : ℕ) (hF : F.IsHomogeneous e) :
    (pullback.snd (a3m_Tκ CX j) (a3m_Tκ CX l)).appTop
        ((Scheme.ΓSpecIso _).inv (a3m_Tθ CX l F)) =
      (pullback.snd (a3m_Tκ CX j) (a3m_Tκ CX l)).appTop
          ((Scheme.ΓSpecIso _).inv (a3m_Tθ CX l (X j))) ^ e *
        (pullback.fst (a3m_Tκ CX j) (a3m_Tκ CX l)).appTop
          ((Scheme.ΓSpecIso _).inv (a3m_Tθ CX j F)) := by
  set f₁ := pullback.fst (a3m_Tκ CX j) (a3m_Tκ CX l)
  set f₂ := pullback.snd (a3m_Tκ CX j) (a3m_Tκ CX l)
  have hcond : f₁ ≫ a3m_Tκ CX j = f₂ ≫ a3m_Tκ CX l := pullback.condition
  set iL := fun m : σ => CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
    (R := ℤ) (A := CX.T m) (B := a3m_Away1))
  set iR := fun m : σ => CommRingCat.ofHom (Algebra.TensorProduct.includeRight
    (R := ℤ) (A := CX.T m) (B := a3m_Away1)).toRingHom
  have hfst : ∀ m, a3m_Tκ CX m ≫ pullback.fst _ _ = Spec.map (iL m) ≫ CX.κ m := fun m =>
    a3m_prodChart_fst (CX.κ m) (g3c_chartι 1 0)
  have hsnd : ∀ m, a3m_Tκ CX m ≫ pullback.snd _ _ = Spec.map (iR m) ≫ g3c_chartι 1 0 :=
    fun m => a3m_prodChart_snd (CX.κ m) (g3c_chartι 1 0)
  have hρ : (f₁ ≫ Spec.map (iL j)) ≫ CX.κ j = (f₂ ≫ Spec.map (iL l)) ≫ CX.κ l := by
    rw [Category.assoc, Category.assoc, ← hfst, ← hfst, ← Category.assoc, ← Category.assoc,
      hcond]
  let ρ := pullback.lift _ _ hρ
  have ht : f₁ ≫ Spec.map (iR j) = f₂ ≫ Spec.map (iR l) := by
    rw [← cancel_mono (g3c_chartι 1 0), Category.assoc, Category.assoc, ← hsnd, ← hsnd,
      ← Category.assoc, ← Category.assoc, hcond]
  have key : ∀ (m : σ) (f : pullback (a3m_Tκ CX j) (a3m_Tκ CX l) ⟶ Spec (a3m_TT CX m))
      (G : MvPolynomial σ ℂ),
      f.appTop ((Scheme.ΓSpecIso _).inv (a3m_Tθ CX m (MvPolynomial.map Polynomial.C G))) =
        (f ≫ Spec.map (iL m)).appTop ((Scheme.ΓSpecIso _).inv (CX.θ m G)) := by
    intro m f G
    rw [a3m_Tθ_map_C, a3m_appTop_comp_SpecMap]
    rfl
  have hX0 : ∀ G : MvPolynomial σ ℂ, G.IsHomogeneous 1 ∨ G.IsHomogeneous 0 →
      ∀ e', G.IsHomogeneous e' →
      f₂.appTop ((Scheme.ΓSpecIso _).inv (a3m_Tθ CX l (MvPolynomial.map Polynomial.C G))) =
        (f₂.appTop ((Scheme.ΓSpecIso _).inv (a3m_Tθ CX l (X j)))) ^ e' *
          f₁.appTop ((Scheme.ΓSpecIso _).inv (a3m_Tθ CX j (MvPolynomial.map Polynomial.C G))) := by
    intro G _ e' hG
    have h := congrArg ρ.appTop.hom (hovX j l G e' hG)
    rw [map_mul, map_pow, ← a3m_appTop_comp_apply, ← a3m_appTop_comp_apply,
      ← a3m_appTop_comp_apply, pullback.lift_fst, pullback.lift_snd] at h
    have hXj : a3m_Tθ CX l (X j) = a3m_Tθ CX l (MvPolynomial.map Polynomial.C (X j)) := by
      rw [MvPolynomial.map_X]
    rw [key, key, hXj, key]
    exact h
  let φ : MvPolynomial σ (Polynomial ℂ) →+* Γ(pullback (a3m_Tκ CX j) (a3m_Tκ CX l), ⊤) :=
    f₂.appTop.hom.comp ((Scheme.ΓSpecIso _).inv.hom.comp (a3m_Tθ CX l))
  let ψ : MvPolynomial σ (Polynomial ℂ) →+* Γ(pullback (a3m_Tκ CX j) (a3m_Tκ CX l), ⊤) :=
    f₁.appTop.hom.comp ((Scheme.ΓSpecIso _).inv.hom.comp (a3m_Tθ CX j))
  have hC : ∀ r : Polynomial ℂ, φ (MvPolynomial.C r) = ψ (MvPolynomial.C r) := by
    have : φ.comp MvPolynomial.C = ψ.comp MvPolynomial.C := by
      refine Polynomial.ringHom_ext (fun c => ?_) ?_
      · have h := hX0 (MvPolynomial.C c) (Or.inr (isHomogeneous_C _ _)) 0 (isHomogeneous_C _ _)
        rw [pow_zero, one_mul, MvPolynomial.map_C] at h
        exact h
      · simp only [φ, ψ, RingHom.comp_apply, a3m_Tθ, coe_eval₂Hom, eval₂_C,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
        change f₂.appTop ((Scheme.ΓSpecIso _).inv ((iR l).hom a3m_t₁)) =
          f₁.appTop ((Scheme.ΓSpecIso _).inv ((iR j).hom a3m_t₁))
        rw [← a3m_appTop_comp_SpecMap, ← a3m_appTop_comp_SpecMap, ht]
    exact fun r => congrArg (fun g : Polynomial ℂ →+* _ => g r) this
  have hX : ∀ k, φ (X k) = φ (X j) * ψ (X k) := by
    intro k
    have h := hX0 (X k) (Or.inl (isHomogeneous_X _ _)) 1 (isHomogeneous_X _ _)
    rw [pow_one, MvPolynomial.map_X] at h
    exact h
  exact a3m_twist φ ψ (φ (X j)) hC hX F e hF

/-- The open subscheme `X × 𝔸¹ = X × D₊(s₀)` of `X × ℙ¹_ℤ`. -/
def a3m_U (Xs : Scheme.{0}) : (a3m_T Xs).Opens :=
  (pullback.snd (terminal.from Xs) (terminal.from (g3c_P 1))) ⁻¹ᵁ (g3c_chartι 1 0).opensRange

theorem a3m_range_Tκ_subset (j : σ) : Set.range (a3m_Tκ CX j) ⊆ a3m_U Xs := by
  rintro _ ⟨p, rfl⟩
  change pullback.snd (terminal.from Xs) (terminal.from (g3c_P 1)) (a3m_Tκ CX j p) ∈
    Set.range (g3c_chartι 1 0)
  rw [← Scheme.Hom.comp_apply,
    show a3m_Tκ CX j ≫ pullback.snd (terminal.from Xs) (terminal.from (g3c_P 1)) = _ from
      a3m_prodChart_snd (CX.κ j) (g3c_chartι 1 0)]
  exact ⟨_, rfl⟩

theorem a3m_U_cover (y : a3m_T Xs) (hy : y ∈ a3m_U Xs) : ∃ j, y ∈ Set.range (a3m_Tκ CX j) := by
  obtain ⟨j, hj⟩ := CX.cover (pullback.fst (terminal.from Xs) (terminal.from (g3c_P 1)) y)
  refine ⟨j, ?_⟩
  change y ∈ Set.range (a3m_prodChart (CX.κ j) (g3c_chartι 1 0))
  rw [a3m_range_prodChart]
  exact ⟨hj, hy⟩

/-- The projective charts of `X × 𝔸¹`. -/
def a3m_lineCharts [Fintype σ]
    (hovX : ∀ (j l : σ) (F : MvPolynomial σ ℂ) (e : ℕ), F.IsHomogeneous e →
      (pullback.snd (CX.κ j) (CX.κ l)).appTop ((Scheme.ΓSpecIso _).inv (CX.θ l F)) =
        (pullback.snd (CX.κ j) (CX.κ l)).appTop ((Scheme.ΓSpecIso _).inv (CX.θ l (X j))) ^ e *
          (pullback.fst (CX.κ j) (CX.κ l)).appTop ((Scheme.ΓSpecIso _).inv (CX.θ j F))) :
    a3m_SpecCharts (a3m_U Xs).toScheme σ (Polynomial ℂ) :=
  a3m_SpecCharts.ofOpen (a3m_U Xs) (a3m_TT CX) (a3m_Tκ CX) (a3m_range_Tκ_subset CX)
    (a3m_U_cover CX) (a3m_Tθ CX) (a3m_Tθ_X_self CX) (a3m_Tθ_surj CX) (a3m_Tinter CX)
    (a3m_compat_of_overlap (a3m_Tκ CX) (a3m_Tθ CX) (a3m_Tinter CX) (a3m_Thov CX hovX))

variable [Fintype σ]
  (hovX : ∀ (j l : σ) (F : MvPolynomial σ ℂ) (e : ℕ), F.IsHomogeneous e →
      (pullback.snd (CX.κ j) (CX.κ l)).appTop ((Scheme.ΓSpecIso _).inv (CX.θ l F)) =
        (pullback.snd (CX.κ j) (CX.κ l)).appTop ((Scheme.ΓSpecIso _).inv (CX.θ l (X j))) ^ e *
          (pullback.fst (CX.κ j) (CX.κ l)).appTop ((Scheme.ΓSpecIso _).inv (CX.θ j F)))

theorem a3m_lineCharts_κ (j : σ) :
    (a3m_lineCharts CX hovX).κ j ≫ (a3m_U Xs).ι = a3m_Tκ CX j :=
  a3m_SpecCharts.ofOpen_κ _ _ _ _ _ _ _ _ _ _ j

theorem a3m_lineCharts_pt (y : (a3m_U Xs).toScheme) :
    ∃ (j : σ) (p : Spec (a3m_TT CX j)), (a3m_lineCharts CX hovX).κ j p = y ∧
      (a3m_U Xs).ι y = a3m_Tκ CX j p := by
  obtain ⟨j, p, hp⟩ := (a3m_lineCharts CX hovX).cover y
  refine ⟨j, p, hp, ?_⟩
  rw [← hp, ← Scheme.Hom.comp_apply, a3m_lineCharts_κ]
  rfl

/-- The point of `X` under a point of `X × 𝔸¹` has the contracted prime. -/
theorem a3m_line_prime_fst (y : (a3m_U Xs).toScheme) :
    CX.prime (pullback.fst (terminal.from Xs) (terminal.from (g3c_P 1)) ((a3m_U Xs).ι y)) =
      ((a3m_lineCharts CX hovX).prime y).comap (MvPolynomial.map Polynomial.C) := by
  obtain ⟨j, p, hp, hz⟩ := a3m_lineCharts_pt CX hovX y
  have hfst : pullback.fst (terminal.from Xs) (terminal.from (g3c_P 1)) ((a3m_U Xs).ι y) =
      CX.κ j (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := ℤ) (A := CX.T j) (B := a3m_Away1))) p) := by
    rw [hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    exact congrArg (fun f => f p) (a3m_prodChart_fst (CX.κ j) (g3c_chartι 1 0))
  ext G
  rw [Ideal.mem_comap, (a3m_lineCharts CX hovX).mem_prime_iff y j p hp,
    CX.mem_prime_iff _ j _ hfst.symm]
  refine forall_congr' fun e => ?_
  change CX.θ j _ ∈ Ideal.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ)
    (A := CX.T j) (B := a3m_Away1)) p.asIdeal ↔ _
  rw [Ideal.mem_comap, a3m_homogeneousComponent_map]
  change _ ↔ a3m_Tθ CX j _ ∈ p.asIdeal
  rw [a3m_Tθ_map_C]

theorem a3m_line_snd (y : (a3m_U Xs).toScheme) :
    ∃ (j : σ) (p : Spec (a3m_TT CX j)), (a3m_lineCharts CX hovX).κ j p = y ∧
      pullback.snd (terminal.from Xs) (terminal.from (g3c_P 1)) ((a3m_U Xs).ι y) =
        g3c_chartι 1 0 (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := ℤ) (A := CX.T j) (B := a3m_Away1)).toRingHom) p) := by
  obtain ⟨j, p, hp, hz⟩ := a3m_lineCharts_pt CX hovX y
  refine ⟨j, p, hp, ?_⟩
  rw [hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  exact congrArg (fun f => f p) (a3m_prodChart_snd (CX.κ j) (g3c_chartι 1 0))

theorem a3m_line_mem_Z (y : (a3m_U Xs).toScheme) (a : a3m_Away1) (f : Polynomial ℂ)
    (haf : ∀ (j : σ), a3m_Tθ CX j (MvPolynomial.C f) =
      Algebra.TensorProduct.includeRight (R := ℤ) (A := CX.T j) a) :
    (∃ q : Spec (.of a3m_Away1), g3c_chartι 1 0 q =
        pullback.snd (terminal.from Xs) (terminal.from (g3c_P 1)) ((a3m_U Xs).ι y) ∧
        a ∈ q.asIdeal) ↔ MvPolynomial.C f ∈ (a3m_lineCharts CX hovX).prime y := by
  obtain ⟨j, p, hp, hsnd⟩ := a3m_line_snd CX hovX y
  rw [a3m_SpecCharts.mem_prime_iff_of_isHomogeneous _ y j p hp _ 0 (isHomogeneous_C _ _)]
  change _ ↔ a3m_Tθ CX j (MvPolynomial.C f) ∈ p.asIdeal
  rw [haf j, hsnd]
  constructor
  · rintro ⟨q, hq, ha⟩
    have := (g3c_chartι 1 0).isOpenEmbedding.injective hq
    rw [this] at ha
    exact ha
  · intro ha
    exact ⟨_, rfl, ha⟩

theorem a3m_line_mem_Z0 (y : (a3m_U Xs).toScheme) :
    pullback.snd (terminal.from Xs) (terminal.from (g3c_P 1)) ((a3m_U Xs).ι y) ∈ a3m_Z0 ↔
      MvPolynomial.C Polynomial.X ∈ (a3m_lineCharts CX hovX).prime y := by
  have := a3m_line_mem_Z CX hovX y a3m_t₁ Polynomial.X (fun j => by
    simp only [a3m_Tθ, coe_eval₂Hom, eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X])
  rw [← this]
  exact ⟨fun ⟨q, hq, ha⟩ => ⟨q, hq, ha⟩, fun ⟨q, hq, ha⟩ => ⟨q, hq, ha⟩⟩

theorem a3m_line_mem_Zinf (y : (a3m_U Xs).toScheme) :
    pullback.snd (terminal.from Xs) (terminal.from (g3c_P 1)) ((a3m_U Xs).ι y) ∈ a3m_Zinf ↔
      MvPolynomial.C (Polynomial.X - 1) ∈ (a3m_lineCharts CX hovX).prime y := by
  have := a3m_line_mem_Z CX hovX y (a3m_t₁ - 1) (Polynomial.X - 1) (fun j => by
    simp only [a3m_Tθ, coe_eval₂Hom, eval₂_C, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, map_sub, map_one])
  rw [← this]
  exact ⟨fun ⟨q, hq, ha⟩ => ⟨q, hq, ha⟩, fun ⟨q, hq, ha⟩ => ⟨q, hq, ha⟩⟩

theorem a3m_includeRight_evt (j : σ) (f : Polynomial ℤ) :
    Algebra.TensorProduct.includeRight (R := ℤ) (A := CX.T j) (a3m_evt f) =
      a3m_Tθ CX j (MvPolynomial.C (f.map (Int.castRingHom ℂ))) := by
  set f₁ := (Algebra.TensorProduct.includeRight (R := ℤ) (A := CX.T j)
    (B := a3m_Away1)).toRingHom.comp a3m_evt
  set f₂ := (a3m_Tθ CX j).comp (MvPolynomial.C.comp (Polynomial.mapRingHom (Int.castRingHom ℂ)))
  have : f₁ = f₂ := by
    refine Polynomial.ringHom_ext (fun n => ?_) ?_
    · exact congrArg (fun φ : ℤ →+* a3m_TT CX j => φ n)
        (RingHom.ext_int (f₁.comp Polynomial.C) (f₂.comp Polynomial.C))
    · simp [f₁, f₂, a3m_evt, a3m_Tθ]
  exact congrArg (fun φ : Polynomial ℤ →+* a3m_TT CX j => φ f) this

/-- A point of `X × 𝔸¹` whose prime meets `ℂ[t]` only in `0` lies over the generic point of the
affine line. -/
theorem a3m_line_snd_bot (y : (a3m_U Xs).toScheme)
    (hdom : ∀ f : Polynomial ℂ, f ≠ 0 → MvPolynomial.C f ∉ (a3m_lineCharts CX hovX).prime y) :
    pullback.snd (terminal.from Xs) (terminal.from (g3c_P 1)) ((a3m_U Xs).ι y) =
      g3c_chartι 1 0 a3m_bot1 := by
  obtain ⟨j, p, hp, hsnd⟩ := a3m_line_snd CX hovX y
  rw [hsnd]
  congr 1
  apply PrimeSpectrum.ext
  ext a
  change a ∈ Ideal.comap (Algebra.TensorProduct.includeRight (R := ℤ) (A := CX.T j)
    (B := a3m_Away1)).toRingHom p.asIdeal ↔ a ∈ (⊥ : Ideal a3m_Away1)
  rw [Ideal.mem_comap, Ideal.mem_bot]
  refine ⟨fun ha => ?_, fun ha => by rw [ha, map_zero]; exact zero_mem _⟩
  obtain ⟨P, rfl⟩ := a3m_awayCoord_surj 1 0 a
  rw [← a3m_evt_ψZ, RingHom.comp_apply] at ha ⊢
  change Algebra.TensorProduct.includeRight (R := ℤ) (A := CX.T j) _ ∈ p.asIdeal at ha
  rw [a3m_includeRight_evt] at ha
  have hC : MvPolynomial.C ((a3m_ψZ P).map (Int.castRingHom ℂ)) ∈
      (a3m_lineCharts CX hovX).prime y :=
    ((a3m_lineCharts CX hovX).mem_prime_iff_of_isHomogeneous y j p hp _ 0
      (isHomogeneous_C _ _)).2 ha
  by_contra hne
  have hf : (a3m_ψZ P).map (Int.castRingHom ℂ) ≠ 0 := by
    intro h0
    apply hne
    have : a3m_ψZ P = 0 := Polynomial.map_injective _ (Int.cast_injective) (by rw [h0, Polynomial.map_zero])
    rw [this, map_zero]
  exact hdom _ hf hC

omit [Fintype σ] in
theorem a3m_Tθ_eq_comp [Fintype σ] [DecidableEq σ] (j : σ) :
    (a3m_Tθ CX j).comp (a3m_eq σ).toRingHom =
      (Polynomial.eval₂RingHom
        (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := CX.T j) (B := a3m_Away1))
        (Algebra.TensorProduct.includeRight (R := ℤ) (A := CX.T j) a3m_t₁)).comp
        (Polynomial.mapRingHom (CX.θ j)) := by
  refine Polynomial.ringHom_ext (fun F => ?_) ?_
  · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    change a3m_Tθ CX j (a3m_eq σ (Polynomial.C F)) = _
    rw [a3m_eq_C, a3m_Tθ_map_C]
  · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    change a3m_Tθ CX j (a3m_eq σ Polynomial.X) = _
    rw [a3m_eq_X]
    simp [a3m_Tθ]

omit [Fintype σ] in
theorem a3m_Tθ_eq_zero_iff [Fintype σ] [DecidableEq σ] (j : σ) (H : Polynomial (MvPolynomial σ ℂ)) :
    a3m_Tθ CX j (a3m_eq σ H) = 0 ↔ ∀ i, CX.θ j (H.coeff i) = 0 := by
  have h := congrArg (fun φ : Polynomial (MvPolynomial σ ℂ) →+* a3m_TT CX j => φ H)
    (a3m_Tθ_eq_comp CX j)
  simp only [RingHom.comp_apply] at h
  change a3m_Tθ CX j (a3m_eq σ H) = _ at h
  rw [h, ← map_zero (Polynomial.eval₂RingHom
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := CX.T j) (B := a3m_Away1))
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := CX.T j) a3m_t₁)),
    (a3m_tensor_eval₂_injective (CX.T j)).eq_iff, Polynomial.coe_mapRingHom,
    Polynomial.ext_iff]
  simp

end LineCharts

theorem a3m_coeff_eq {σ : Type} [Fintype σ] [DecidableEq σ] (H : Polynomial (MvPolynomial σ ℂ))
    (m : σ →₀ ℕ) (i : ℕ) :
    ((a3m_eq σ H).coeff m).coeff i = (H.coeff i).coeff m := by
  induction H using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, MvPolynomial.coeff_add, Polynomial.coeff_add, hp, hq,
      Polynomial.coeff_add, MvPolynomial.coeff_add]
  | monomial n F =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, a3m_eq_C, a3m_eq_X, ← map_pow,
      mul_comm, MvPolynomial.coeff_C_mul, coeff_map, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_X_pow_mul', Polynomial.coeff_C]
    split_ifs with h1 h2 h3 <;> first | (exfalso; omega) | simp_all

theorem a3m_isHomogeneous_coeff {σ : Type} [Fintype σ] [DecidableEq σ]
    (H : Polynomial (MvPolynomial σ ℂ)) (e : ℕ) (hG : (a3m_eq σ H).IsHomogeneous e) (i : ℕ) :
    (H.coeff i).IsHomogeneous e := by
  intro m hm
  apply hG
  intro h0
  apply hm
  rw [← a3m_coeff_eq, h0, Polynomial.coeff_zero]

end HodgeLean.Adapters
