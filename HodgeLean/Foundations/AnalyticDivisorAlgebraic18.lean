import HodgeLean.Foundations.AnalyticDivisorAlgebraic18Proofs

/-! # The hypersurface Nullstellensatz and nearby coprimality

This stage specifies the implication from preparation, discriminant nonvanishing, root counting,
and identity extension to divisibility for an irreducible hypersurface germ. The composition and
finite open shrinking have proofs relative to the separate auxiliary statements. The exact
reduced-equation target and selected-factor propagation remain separate proof obligations.
Analytic spaces, global divisor sheaves, algebraization and cycle classes are outside this scope.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Filter Set Topology
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic18

open AnalyticDivisorAlgebraic4 AnalyticDivisorAlgebraic5
open AnalyticDivisorAlgebraic6 AnalyticDivisorAlgebraic7 AnalyticDivisorAlgebraic11

/-- Preparation in a regular last coordinate, including irreducibility of the prepared equation.
Source: Gunning--Rossi, II.B, Lemma 1 and Theorems 2--4;
`AnalyticDivisorAlgebraic6.spec_exists_linearChange_regular`, `spec_preparation_transfer`,
`spec_irreducible_transfer`; `AnalyticDivisorAlgebraic8.productAnalyticGermUFD`. -/
theorem gaga18_prepare (n : ℕ) (p : Fin n → ℂ)
    (g : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g p) (hi : IsIrreducibleAt g p) :
    ∃ m : ℕ, ∃ L : (Fin n → ℂ) ≃L[ℂ] ((Fin m → ℂ) × ℂ),
    ∃ d : ℕ, 0 < d ∧ ∃ u : (Fin m → ℂ) × ℂ → ℂ,
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      ∃ a : Fin d → (Fin m → ℂ) → ℂ,
        (∀ j, AnalyticAt ℂ (a j) 0 ∧ a j 0 = 0) ∧
        analyticOrderAt (fun w : ℂ ↦ g (p + L.symm (0, w))) 0 = d ∧
        IsIrreducibleAt (monicInLast a) 0 ∧
        (fun y ↦ g (p + L.symm y)) =ᶠ[𝓝 0] fun y ↦ u y * monicInLast a y :=
  gaga18_prepare_aux n p g hg hi

/-- An irreducible Weierstrass equation has a discriminant which is not the zero germ.
Source: Gunning--Rossi, II.B, Theorems 3--6; III.A, Theorem 1;
`AnalyticDivisorAlgebraic6.spec_irreducible_transfer`, `spec_eventually_isSquareFreeAt`,
`AnalyticDivisorAlgebraic5.spec_weierstrassDiscr_not_eventually_zero`. -/
theorem gaga18_discriminant (m d : ℕ) (a : Fin d → (Fin m → ℂ) → ℂ)
    (hd : 0 < d) (ha : ∀ j, AnalyticAt ℂ (a j) 0 ∧ a j 0 = 0)
    (hi : IsIrreducibleAt (monicInLast a) 0) :
    ¬ ∀ᶠ z in 𝓝 0, weierstrassDiscr a z = 0 :=
  gaga18_discriminant_aux m d a hd ha hi

/-- Off the discriminant, all roots lie in the division neighbourhood and kill the remainder.
The displayed polynomial has degree below the divisor degree, hence is zero on these fibres.
Source: Gunning--Rossi, II.B, Theorems 3--4;
`AnalyticDivisorAlgebraic4.spec_weierstrass_division`, `spec_monicInLast_roots_small`;
`AnalyticDivisorAlgebraic5.spec_weierstrassDiscr_ne_zero_iff`. -/
theorem gaga18_remainder_roots (m d : ℕ) (hd : 0 < d)
    (a b : Fin d → (Fin m → ℂ) → ℂ) (H q : (Fin m → ℂ) × ℂ → ℂ)
    (ha : ∀ j, AnalyticAt ℂ (a j) 0 ∧ a j 0 = 0)
    (hb : ∀ j, AnalyticAt ℂ (b j) 0)
    (hH : AnalyticAt ℂ H 0) (hq : AnalyticAt ℂ q 0)
    (hdiv : H =ᶠ[𝓝 0] fun y ↦ q y * monicInLast a y + ∑ j, b j y.1 * y.2 ^ (j : ℕ))
    (hz : ∀ᶠ y in 𝓝 0, monicInLast a y = 0 → H y = 0) :
    ∀ᶠ z in 𝓝 0, weierstrassDiscr a z ≠ 0 →
      (∃ roots : Fin d → ℂ, Function.Injective roots ∧
        ∀ i, (monicPoly a z).eval (roots i) = 0 ∧
          (∑ j : Fin d, Polynomial.C (b j z) * Polynomial.X ^ (j : ℕ)).eval (roots i) = 0) ∧
      (∑ j : Fin d, Polynomial.C (b j z) * Polynomial.X ^ (j : ℕ)).degree < (d : WithBot ℕ) ∧
      ∀ j, b j z = 0 :=
  gaga18_remainder_roots_aux m d hd a b H q ha hb hH hq hdiv hz

/-- Identity-theorem extension of each analytic remainder coefficient across the discriminant.
Source: Gunning--Rossi, I.A, Theorem 6;
`AnalyticDivisorAlgebraic12.spec_germ_ne_zero_of_preconnected`. -/
theorem gaga18_extend (m d : ℕ) (a b : Fin d → (Fin m → ℂ) → ℂ)
    (ha : ∀ j, AnalyticAt ℂ (a j) 0) (hb : ∀ j, AnalyticAt ℂ (b j) 0)
    (hΔ : ¬ ∀ᶠ z in 𝓝 0, weierstrassDiscr a z = 0)
    (hoff : ∀ᶠ z in 𝓝 0, weierstrassDiscr a z ≠ 0 → ∀ j, b j z = 0) :
    ∀ᶠ z in 𝓝 0, ∀ j, b j z = 0 :=
  gaga18_extend_aux m d a b ha hb hΔ hoff

/-- Coprimality propagates for one pair. The selected-factor decompositions at `q` are
quantified separately; their irreducible factors cannot match across the two groups.
Source: Gunning--Rossi, II.B, Theorems 3--6 and III.A, Theorem 1;
`AnalyticDivisorAlgebraic14.spec_exists_irreducible_decomposition_at`,
`AnalyticDivisorAlgebraic17.spec_nearby_factor_matching`,
`AnalyticDivisorAlgebraic7.spec_irreducible_decomposition_unique`,
`spec_hypersurface_nullstellensatz_aux`. -/
theorem gaga18_pair_propagation (n : ℕ) (p : Fin n → ℂ)
    (F G : (Fin n → ℂ) → ℂ) (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (hiF : IsIrreducibleAt F p) (hiG : IsIrreducibleAt G p)
    (hc : IsCoprimeAt F G p) :
    ∀ᶠ q in 𝓝 p, IsCoprimeAt F G q ∧
      ∀ (k l : ℕ) (u v : (Fin n → ℂ) → ℂ)
        (Q : Fin k → (Fin n → ℂ) → ℂ) (R : Fin l → (Fin n → ℂ) → ℂ)
        (d : Fin k → ℕ) (e : Fin l → ℕ),
        AnalyticAt ℂ u q → u q ≠ 0 → AnalyticAt ℂ v q → v q ≠ 0 →
        (∀ j, AnalyticAt ℂ (Q j) q ∧ IsIrreducibleAt (Q j) q ∧ 0 < d j) →
        (∀ j, AnalyticAt ℂ (R j) q ∧ IsIrreducibleAt (R j) q ∧ 0 < e j) →
        Pairwise (fun j j' ↦ IsCoprimeAt (Q j) (Q j') q) →
        Pairwise (fun j j' ↦ IsCoprimeAt (R j) (R j') q) →
        (F =ᶠ[𝓝 q] fun z ↦ u z * ∏ j, Q j z ^ d j) →
        (G =ᶠ[𝓝 q] fun z ↦ v z * ∏ j, R j z ^ e j) →
        ∀ j j', ¬ AreAssociatedAt (Q j) (R j') q :=
  gaga18_pair_propagation_aux n p F G hF hG hiF hiG hc

/-- The two coordinate factors of the crossing, with coprimality at the origin.
Source: Gunning--Rossi, II.B, Theorems 3--6;
`AnalyticDivisorAlgebraic17.gaga17_crossing_data`, transported to `Fin 2` coordinates. -/
theorem gaga18_coordinate_data :
    (∀ i : Fin 2, AnalyticAt ℂ (fun z : Fin 2 → ℂ ↦ z i) 0 ∧
      IsIrreducibleAt (fun z : Fin 2 → ℂ ↦ z i) 0) ∧
    Pairwise (fun i j : Fin 2 ↦ IsCoprimeAt (fun z : Fin 2 → ℂ ↦ z i)
      (fun z : Fin 2 → ℂ ↦ z j) 0) :=
  gaga18_coordinate_data_aux

/-- Squarefreeness of a coordinate germ and its specified analytic unit multiple.
Source: Gunning--Rossi, II.B, Theorems 3--6 (units preserve irreducible elements). -/
theorem gaga18_reduced_unit_data
    (hf : AnalyticAt ℂ gaga18_axis 0)
    (hug : AnalyticAt ℂ (fun z ↦ gaga18_unit z * gaga18_axis z) 0) :
    Squarefree (⟨Filter.Germ.ofFun gaga18_axis, gaga18_axis, hf, rfl⟩ : AnalyticGermAt 2 0) ∧
    Squarefree (⟨Filter.Germ.ofFun (fun z ↦ gaga18_unit z * gaga18_axis z),
      (fun z ↦ gaga18_unit z * gaga18_axis z), hug, rfl⟩ : AnalyticGermAt 2 0) :=
  gaga18_reduced_unit_data_aux hf hug

/-- The cusp is analytic and irreducible, despite its singularity at the origin.
Source: Gunning--Rossi, II.B, Theorems 3--6, applied to the Weierstrass polynomial `w²-z³`. -/
theorem gaga18_cusp_irreducible :
    AnalyticAt ℂ gaga18_cusp 0 ∧ IsIrreducibleAt gaga18_cusp 0 :=
  gaga18_cusp_irreducible_aux

/-- The node splits into two regular analytic branches using the local square root of `1+z₁`.
Source: Gunning--Rossi, II.B, Theorem 2 and Theorems 3--6 (local analytic factorization). -/
theorem gaga18_node_factorization :
    ∃ s : (Fin 2 → ℂ) → ℂ, AnalyticAt ℂ s 0 ∧ s 0 = 1 ∧
      (∀ᶠ z in 𝓝 0, s z ^ 2 = 1 + z 0) ∧
      (gaga18_node =ᶠ[𝓝 0] fun z ↦ (z 1 - z 0 * s z) * (z 1 + z 0 * s z)) ∧
      IsIrreducibleAt (fun z ↦ z 1 - z 0 * s z) 0 ∧
      IsIrreducibleAt (fun z ↦ z 1 + z 0 * s z) 0 ∧
      ¬ IsIrreducibleAt gaga18_node 0 :=
  gaga18_node_factorization_aux

/-- A function vanishing on an irreducible hypersurface germ is divisible by its equation.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, III.A, Theorem 1
(Nullstellensatz for prime ideals), with II.B, Theorems 2--4 (preparation and division) and
I.A, Theorem 6 (identity theorem). -/
theorem spec_hypersurface_nullstellensatz (n : ℕ) (p : Fin n → ℂ)
    (g h : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g p) (hh : AnalyticAt ℂ h p)
    (hgi : IsIrreducibleAt g p) (hz : ∀ᶠ z in 𝓝 p, g z = 0 → h z = 0) :
    ∃ c : (Fin n → ℂ) → ℂ, AnalyticAt ℂ c p ∧ h =ᶠ[𝓝 p] fun z ↦ g z * c z :=
  spec_hypersurface_nullstellensatz_aux n p g h hg hh hgi hz

/-- Reduced local equations with the same zero germ differ by a unit.  The binders and conclusion
match the stage-five assembly target.
Source: Gunning--Rossi, III.A, Theorem 1 and II.B, Theorems 3--6. -/
theorem spec_reduced_zero_germs_associated (n : ℕ) (p : Fin n → ℂ)
    (f g : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hfr : Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p))
    (hgr : Squarefree (⟨Filter.Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p))
    (hz : ∀ᶠ z in 𝓝 p, f z = 0 ↔ g z = 0) : AreAssociatedAt f g p :=
  spec_reduced_zero_germs_associated_aux n p f g hf hg hfr hgr hz

/-- After shrinking around `p`, distinct irreducible factors at `p` have no common irreducible
factor at any point of the chosen neighbourhood.
Source: Gunning--Rossi, III.A, Theorem 1; II.B, Theorems 3--6; and the finite matching argument
of stage seventeen. -/
theorem spec_eventually_pairwise_coprime (n r : ℕ) (p : Fin n → ℂ)
    (P : Fin r → (Fin n → ℂ) → ℂ) (hP : ∀ a, AnalyticAt ℂ (P a) p)
    (hiP : ∀ a, IsIrreducibleAt (P a) p)
    (hcP : Pairwise (fun a b ↦ IsCoprimeAt (P a) (P b) p)) :
    ∃ N, IsOpen N ∧ p ∈ N ∧ ∀ q ∈ N, ∀ a b, a ≠ b →
      ¬ ∃ A s t : (Fin n → ℂ) → ℂ, AnalyticAt ℂ A q ∧ IsIrreducibleAt A q ∧
        AnalyticAt ℂ s q ∧ (P a =ᶠ[𝓝 q] fun z ↦ A z * s z) ∧
        AnalyticAt ℂ t q ∧ (P b =ᶠ[𝓝 q] fun z ↦ A z * t z) :=
  spec_eventually_pairwise_coprime_aux n r p P hP hiP hcP

/-- Analyticity and local factor behavior of the coordinate, crossing, cusp, node, and unit
fixtures used below.
Source: Gunning--Rossi, II.B, Theorems 2--6 and III.A, Theorem 1. -/
theorem gaga18_concrete_data :
    AnalyticAt ℂ gaga18_axis 0 ∧ IsIrreducibleAt gaga18_axis 0 ∧
    AnalyticAt ℂ gaga18_crossing 0 ∧
    AnalyticAt ℂ gaga18_cusp 0 ∧ IsIrreducibleAt gaga18_cusp 0 ∧
    AnalyticAt ℂ gaga18_node 0 ∧ ¬ IsIrreducibleAt gaga18_node 0 ∧
    AnalyticAt ℂ gaga18_unit 0 ∧ gaga18_unit 0 ≠ 0 :=
  gaga18_concrete_data_aux

-- The irreducible cusp divides its square from zero-set containment.
example : ∃ c : (Fin 2 → ℂ) → ℂ, AnalyticAt ℂ c 0 ∧
    (fun z ↦ gaga18_cusp z ^ 2) =ᶠ[𝓝 0] fun z ↦ gaga18_cusp z * c z := by
  apply spec_hypersurface_nullstellensatz 2 0
  · exact gaga18_concrete_data.2.2.2.1
  · exact gaga18_concrete_data.2.2.2.1.pow 2
  · exact gaga18_concrete_data.2.2.2.2.1
  · filter_upwards [] with z
    intro hz
    simp [hz]

-- The concrete data also detects a unit, a crossing, and an analytically reducible node.
example : AnalyticAt ℂ gaga18_unit 0 ∧ gaga18_unit 0 ≠ 0 ∧
    AnalyticAt ℂ gaga18_crossing 0 ∧ ¬ IsIrreducibleAt gaga18_node 0 :=
  ⟨gaga18_concrete_data.2.2.2.2.2.2.2.1,
    gaga18_concrete_data.2.2.2.2.2.2.2.2,
    gaga18_concrete_data.2.2.1,
    gaga18_concrete_data.2.2.2.2.2.2.1⟩

-- Axis-square Nullstellensatz witness, with every premise constructed.
example : ∃ c : (Fin 2 → ℂ) → ℂ, AnalyticAt ℂ c 0 ∧
    (fun z ↦ gaga18_axis z ^ 2) =ᶠ[𝓝 0] fun z ↦ gaga18_axis z * c z := by
  apply spec_hypersurface_nullstellensatz 2 0 _ _
    (gaga18_coordinate_data.1 0).1 ((gaga18_coordinate_data.1 0).1.pow 2)
    (gaga18_coordinate_data.1 0).2
  exact Eventually.of_forall fun z hz ↦ by
    change z 0 ^ 2 = 0
    rw [hz]
    norm_num

-- Preparation is instantiated on the singular irreducible cusp, not on an assumed presentation.
example :
    ∃ m : ℕ, ∃ L : (Fin 2 → ℂ) ≃L[ℂ] ((Fin m → ℂ) × ℂ),
    ∃ d : ℕ, 0 < d ∧ ∃ u : (Fin m → ℂ) × ℂ → ℂ,
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      ∃ a : Fin d → (Fin m → ℂ) → ℂ,
        (∀ j, AnalyticAt ℂ (a j) 0 ∧ a j 0 = 0) ∧
        analyticOrderAt (fun w : ℂ ↦ gaga18_cusp (L.symm (0, w))) 0 = d ∧
        IsIrreducibleAt (monicInLast a) 0 ∧
        (fun y ↦ gaga18_cusp (L.symm y)) =ᶠ[𝓝 0] fun y ↦ u y * monicInLast a y := by
  simpa only [zero_add] using gaga18_prepare 2 0 gaga18_cusp
    gaga18_cusp_irreducible.1 gaga18_cusp_irreducible.2

-- One-variable Weierstrass equation w; its coefficient space has dimension zero.
example : ¬ ∀ᶠ z : Fin 0 → ℂ in 𝓝 0,
    weierstrassDiscr (fun _ : Fin 1 ↦ fun _ : Fin 0 → ℂ ↦ (0 : ℂ)) z = 0 := by
  apply gaga18_discriminant 0 1 _ (by decide) (fun _ ↦ ⟨analyticAt_const, rfl⟩)
  have hp : monicInLast (fun _ : Fin 1 ↦ fun _ : Fin 0 → ℂ ↦ (0 : ℂ)) =
      (fun y : (Fin 0 → ℂ) × ℂ ↦ y.2) := by
    funext y
    simp [monicInLast]
  rw [hp]
  exact (AnalyticDivisorAlgebraic17.gaga17_axis_power_data 0 1 (by decide)).2 0 rfl

-- Root counting for division of w² by w: q=w, remainder zero, one distinct root.
example : ∀ᶠ z : Fin 1 → ℂ in 𝓝 0,
    weierstrassDiscr (fun _ : Fin 1 ↦ fun _ : Fin 1 → ℂ ↦ (0 : ℂ)) z ≠ 0 →
    ∃ roots : Fin 1 → ℂ, Function.Injective roots ∧
      ∀ i, (monicPoly (fun _ : Fin 1 ↦ fun _ : Fin 1 → ℂ ↦ (0 : ℂ)) z).eval (roots i) = 0 := by
  have hr := gaga18_remainder_roots 1 1 (by decide)
    (fun _ _ ↦ 0) (fun _ _ ↦ 0) (fun y ↦ y.2 ^ 2) (fun y ↦ y.2)
    (fun _ ↦ ⟨analyticAt_const, rfl⟩) (fun _ ↦ analyticAt_const)
    (analyticAt_snd.pow 2) analyticAt_snd
    (Eventually.of_forall fun y ↦ by simp [monicInLast, pow_two])
    (Eventually.of_forall fun y hy ↦ by
      have hy0 : y.2 = 0 := by simpa [monicInLast] using hy
      simp only [hy0, zero_pow (by decide : 2 ≠ 0)])
  filter_upwards [hr] with _z hz
  intro hΔ
  obtain ⟨roots, hi, hr⟩ := (hz hΔ).1
  exact ⟨roots, hi, fun i ↦ (hr i).1⟩

-- Identity extension with the degree-one discriminant and an actual analytic zero coefficient.
example : ∀ᶠ _z : Fin 1 → ℂ in 𝓝 0, ∀ _ : Fin 1, (0 : ℂ) = 0 := by
  apply gaga18_extend 1 1 (fun _ _ ↦ 0) (fun _ _ ↦ 0)
    (fun _ ↦ analyticAt_const) (fun _ ↦ analyticAt_const)
  · apply gaga18_discriminant 1 1 _ (by decide) (fun _ ↦ ⟨analyticAt_const, rfl⟩)
    have hp : monicInLast (fun _ : Fin 1 ↦ fun _ : Fin 1 → ℂ ↦ (0 : ℂ)) =
        (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2) := by
      funext y
      simp [monicInLast]
    rw [hp]
    exact (AnalyticDivisorAlgebraic17.gaga17_axis_power_data 1 1 (by decide)).2 0 rfl
  · exact Eventually.of_forall fun _ _ _ ↦ rfl

-- Both selected factors of the crossing instantiate the one-pair propagation theorem.
example : ∀ᶠ q in 𝓝 (0 : Fin 2 → ℂ),
    IsCoprimeAt (fun z : Fin 2 → ℂ ↦ z 0) (fun z : Fin 2 → ℂ ↦ z 1) q := by
  exact (gaga18_pair_propagation 2 0 _ _ (gaga18_coordinate_data.1 0).1
    (gaga18_coordinate_data.1 1).1 (gaga18_coordinate_data.1 0).2
    (gaga18_coordinate_data.1 1).2 (gaga18_coordinate_data.2 (by decide : (0 : Fin 2) ≠ 1))).mono
      fun _ h ↦ h.1

-- Finite uniform shrinking for the crossing's two displayed coordinate factors.
example : ∃ N, IsOpen N ∧ (0 : Fin 2 → ℂ) ∈ N ∧ ∀ q ∈ N, ∀ a b : Fin 2, a ≠ b →
    ¬ ∃ A s t : (Fin 2 → ℂ) → ℂ, AnalyticAt ℂ A q ∧ IsIrreducibleAt A q ∧
      AnalyticAt ℂ s q ∧ ((fun z ↦ z a) =ᶠ[𝓝 q] fun z ↦ A z * s z) ∧
      AnalyticAt ℂ t q ∧ ((fun z ↦ z b) =ᶠ[𝓝 q] fun z ↦ A z * t z) :=
  spec_eventually_pairwise_coprime 2 2 0 (fun a z ↦ z a)
    (fun a ↦ (gaga18_coordinate_data.1 a).1)
    (fun a ↦ (gaga18_coordinate_data.1 a).2) gaga18_coordinate_data.2

-- The reduced-equation corollary on f and u*f, using the nonconstant unit 1+z₁.
example : AreAssociatedAt gaga18_axis (fun z ↦ gaga18_unit z * gaga18_axis z) 0 := by
  have hf := (gaga18_coordinate_data.1 0).1
  have hu : AnalyticAt ℂ gaga18_unit 0 := analyticAt_const.add hf
  have hu0 : gaga18_unit 0 ≠ 0 := by simp [gaga18_unit]
  have hs := gaga18_reduced_unit_data hf (hu.mul hf)
  apply spec_reduced_zero_germs_associated 2 0 _ _ hf (hu.mul hf) hs.1 hs.2
  filter_upwards [hu.continuousAt.eventually_ne hu0] with z hz
  change gaga18_axis z = 0 ↔ gaga18_unit z * gaga18_axis z = 0
  simp only [mul_eq_zero, hz, false_or]

-- The node fixture supplies actual analytic factors through a local square root of 1+z₁.
example : ∃ s : (Fin 2 → ℂ) → ℂ, AnalyticAt ℂ s 0 ∧ s 0 = 1 ∧
    (gaga18_node =ᶠ[𝓝 0] fun z ↦ (z 1 - z 0 * s z) * (z 1 + z 0 * s z)) := by
  obtain ⟨s, hs, hs0, _, hfac, _⟩ := gaga18_node_factorization
  exact ⟨s, hs, hs0, hfac⟩

example (g : (Fin 0 → ℂ) → ℂ) : ¬ IsIrreducibleAt g 0 :=
  gaga18_no_irreducible_zero 0 g

-- The two singleton decompositions at the crossing feed the selected-factor matching conclusion.
example : ¬ AreAssociatedAt (fun z : Fin 2 → ℂ ↦ z 0) (fun z : Fin 2 → ℂ ↦ z 1) 0 := by
  have hp := (gaga18_pair_propagation 2 0 _ _ (gaga18_coordinate_data.1 0).1
    (gaga18_coordinate_data.1 1).1 (gaga18_coordinate_data.1 0).2
    (gaga18_coordinate_data.1 1).2
    (gaga18_coordinate_data.2 (by decide : (0 : Fin 2) ≠ 1))).self_of_nhds
  have h := hp.2 1 1 (fun _ ↦ 1) (fun _ ↦ 1)
    (fun _ z ↦ z 0) (fun _ z ↦ z 1) (fun _ ↦ 1) (fun _ ↦ 1)
    analyticAt_const one_ne_zero analyticAt_const one_ne_zero
    (fun _ ↦ ⟨(gaga18_coordinate_data.1 0).1, (gaga18_coordinate_data.1 0).2, by decide⟩)
    (fun _ ↦ ⟨(gaga18_coordinate_data.1 1).1, (gaga18_coordinate_data.1 1).2, by decide⟩)
    (fun i j hij ↦ False.elim (hij (Subsingleton.elim i j)))
    (fun i j hij ↦ False.elim (hij (Subsingleton.elim i j)))
    (Eventually.of_forall fun _z ↦ by simp)
    (Eventually.of_forall fun _z ↦ by simp)
  exact h 0 0

-- Units and constants cannot be irreducible hypersurface equations at their base point.
example : ¬ IsIrreducibleAt gaga18_unit 0 := by
  intro hi
  have h : gaga18_unit 0 ≠ 0 := by simp [gaga18_unit]
  exact h hi.1

example (n : ℕ) (p : Fin n → ℂ) (c : ℂ) (hc : c ≠ 0) :
    ¬ IsIrreducibleAt (fun _ : Fin n → ℂ ↦ c) p := fun hi ↦ hc hi.1

example (n : ℕ) (p : Fin n → ℂ) :
    ¬ IsIrreducibleAt (fun _ : Fin n → ℂ ↦ (0 : ℂ)) p := by
  intro hi
  have he : (fun _ : Fin n → ℂ ↦ (0 : ℂ)) =ᶠ[𝓝 p] fun _ ↦ (0 : ℂ) * 0 :=
    Eventually.of_forall fun _ ↦ (zero_mul 0).symm
  rcases hi.2 (fun _ ↦ 0) (fun _ ↦ 0) analyticAt_const analyticAt_const he with h | h
  · exact h rfl
  · exact h rfl

end HodgeLean.Foundations.AnalyticDivisorAlgebraic18
