import HodgeLean.Foundations.Program.BraidBridgesTwoProofs

/-! # Braid-certificate bridges, stage two

Implication from regularity to the downstairs map, from certified lasso traces to
crossing words, and from once-crossing loops to a peripheral presentation and an
analytic marking with one common conjugator. Apparent-point filling, the sphere
marking and the path chain are deferred. HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- The rational map avoids the downstairs punctures.
Source: G32 v0.16, §5.2; b65r_phi_sub. -/
theorem b65x_phi_down : ∀ z ∈ b65s_regular,
    b65r_phi z ≠ 0 ∧ b65r_phi z ≠ 5 ∧ b65r_phi z ≠ -7 :=
  b65x_phi_down_aux

example : ∀ z ∈ b65s_regular,
    b65r_phi z ≠ 0 ∧ b65r_phi z ≠ 5 ∧ b65r_phi z ≠ -7 :=
  b65x_phi_down

/-- Continuity on the regular plane.
Source: G32 v0.16, §5.2; b65r_phi_hasDerivAt. -/
theorem b65x_phi_continuousOn : ContinuousOn b65r_phi b65s_regular :=
  b65x_phi_continuousOn_aux

example : ContinuousOn b65r_phi b65s_regular :=
  b65x_phi_continuousOn

/-- Certified words of the based traces.
Source: B65-BRAIDCERT checker D; BraidBridges, rational pieces and crossing intervals. -/
theorem b65x_trace_crossings (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso i s)) (i : Fin 13) :
    b65x_CrossesAs ((δ i).map b65x_phiMap.continuous) (b65x_rawWord i) :=
  b65x_trace_crossings_aux x δ hδ i

example (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso i s)) (i : Fin 13) :
    b65x_CrossesAs ((δ i).map b65x_phiMap.continuous) (b65x_rawWord i) :=
  b65x_trace_crossings x δ hδ i

/-- Once-crossing generators off the cuts.
Source: Hatcher, Algebraic Topology, §1.2, slit-plane generators. -/
theorem b65x_cut_generators (y : b65x_Down) (hy : ∀ k, ¬ b65x_OnCut k y.val) :
    ∃ g : Fin 3 → Path y y, ∀ j, b65x_CrossesAs (g j) [(j, 1)] :=
  b65x_cut_generators_aux y hy

example (y : b65x_Down) (hy : ∀ k, ¬ b65x_OnCut k y.val) :
    ∃ g : Fin 3 → Path y y, ∀ j, b65x_CrossesAs (g j) [(j, 1)] :=
  b65x_cut_generators y hy

/-- Inverse Hurwitz peripherals have the printed presentation and local classes.
Source: B65-BRAIDCERT REPORT §2; b65r_source_peripheral_presentation. -/
theorem b65x_cut_peripheral (y : b65x_Down) (g : Fin 3 → Path y y)
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)]) :
    (List.ofFn (b65x_peripheral y g)).prod = 1 ∧
    (∀ (G : Type) [Group G] (v : Fin 4 → G), (List.ofFn v).prod = 1 →
      ∃! φ : FundamentalGroup b65x_Down y →* G,
        ∀ i, φ (b65x_peripheral y g i) = v i) ∧
    (∀ (M : FundamentalGroup b65x_Down y →*
        ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ),
      (∀ p : Path y y, (M (FundamentalGroup.fromPath ⟦p⟧)).val =
        b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (p.extend t).val)) →
      ∀ i, IsConj (b65r_printedOperatorHom (b4b_generators i))
        (M (b65x_peripheral y g i))) :=
  b65x_cut_peripheral_aux y g hg

example (y : b65x_Down) (g : Fin 3 → Path y y)
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)]) :
    (List.ofFn (b65x_peripheral y g)).prod = 1 ∧
    (∀ (G : Type) [Group G] (v : Fin 4 → G), (List.ofFn v).prod = 1 →
      ∃! φ : FundamentalGroup b65x_Down y →* G,
        ∀ i, φ (b65x_peripheral y g i) = v i) ∧
    (∀ (M : FundamentalGroup b65x_Down y →*
        ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ),
      (∀ p : Path y y, (M (FundamentalGroup.fromPath ⟦p⟧)).val =
        b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (p.extend t).val)) →
      ∀ i, IsConj (b65r_printedOperatorHom (b4b_generators i))
        (M (b65x_peripheral y g i))) :=
  b65x_cut_peripheral y g hg

/-- The cut marking and analytic transport share one conjugator.
Source: B65-BRAIDCERT REPORT §2; Katz, Rigid Local Systems, Theorem 1.1.2; b65r_rigidity. -/
theorem b65x_downstairs_marking (y : b65x_Down) (g : Fin 3 → Path y y)
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)]) :
    ∃ κ : FundamentalGroup b65x_Down y →* b4b_Group,
      (∀ j, κ (FundamentalGroup.fromPath ⟦g j⟧) = b65b_cut j) ∧
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ, ∀ γ : Path y y,
        b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
          C.val * b65r_operator (b4b_toMatrix (κ (FundamentalGroup.fromPath ⟦γ⟧))) *
            (C⁻¹).val :=
  b65x_downstairs_marking_aux y g hg

example (y : b65x_Down) (g : Fin 3 → Path y y)
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)]) :
    ∃ κ : FundamentalGroup b65x_Down y →* b4b_Group,
      (∀ j, κ (FundamentalGroup.fromPath ⟦g j⟧) = b65b_cut j) ∧
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ, ∀ γ : Path y y,
        b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
          C.val * b65r_operator (b4b_toMatrix (κ (FundamentalGroup.fromPath ⟦γ⟧))) *
            (C⁻¹).val :=
  b65x_downstairs_marking y g hg

/-- The inverse Hurwitz tuple has product one independently of the geometry. -/
example (y : b65x_Down) (g : Fin 3 → Path y y) :
    (List.ofFn (b65x_peripheral y g)).prod = 1 := by
  change FundamentalGroup.fromPath ⟦g 0⟧ *
    (FundamentalGroup.fromPath ⟦g 1⟧ *
      (((FundamentalGroup.fromPath ⟦g 1⟧)⁻¹ * FundamentalGroup.fromPath ⟦g 2⟧ *
        FundamentalGroup.fromPath ⟦g 1⟧) *
        ((FundamentalGroup.fromPath ⟦g 0⟧ * FundamentalGroup.fromPath ⟦g 2⟧ *
          FundamentalGroup.fromPath ⟦g 1⟧)⁻¹ * 1))) = 1
  group

/-- Recover the literal cut tuple from the printed peripheral values. -/
example (y : b65x_Down) (g : Fin 3 → Path y y)
    (ρ : FundamentalGroup b65x_Down y →* b4b_Group)
    (hρ : ∀ i, ρ (b65x_peripheral y g i) = b4b_generators i) :
    ∀ j, ρ (FundamentalGroup.fromPath ⟦g j⟧) = b65b_cut j := by
  intro j
  have h0 := hρ 0
  have h1 := hρ 1
  have h2 := hρ 2
  change ρ (FundamentalGroup.fromPath ⟦g 0⟧) = b4b_generators 0 at h0
  change ρ (FundamentalGroup.fromPath ⟦g 1⟧) = b4b_generators 1 at h1
  change ρ ((FundamentalGroup.fromPath ⟦g 1⟧)⁻¹ *
    FundamentalGroup.fromPath ⟦g 2⟧ * FundamentalGroup.fromPath ⟦g 1⟧) =
      b4b_generators 2 at h2
  rw [map_mul, map_mul, map_inv, h1] at h2
  fin_cases j
  · exact h0
  · exact h1
  · change ρ (FundamentalGroup.fromPath ⟦g 2⟧) =
      b4b_generators 1 * b4b_generators 2 * (b4b_generators 1)⁻¹
    rw [← h2]
    group

end HodgeLean.Foundations.Program
