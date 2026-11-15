import HodgeLean.Foundations.Program.BraidBridgesThreeProofs

/-! # Braid-certificate bridges, stage three

Implication from the downstairs cut marking to a sphere marking with named based loops,
through apparent-puncture filling; implication from root witnesses to a based lasso family
along the certified configuration path, its endpoint loops, the two positive event moves and
an isotopy marking; and the two corrected consumers. Not claimed: existence of the trace
family `δ` (it needs the planned regularity and continuity of the traces), surjectivity of the
sphere marking, uniqueness up to inner conjugation, and any statement about a cover family or
the Schlesinger identification. HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Apparent-puncture filling: a loop of the regular plane that is trivial on the sphere minus
the genuine branch points has trivial downstairs marking value. The apparent poles 3, 1, −2 and
source infinity carry trivial pullback transport, so the marking kills their peripheral classes.
Source: Hatcher, Algebraic Topology, §1.2, Proposition 1.26; b65t_puncture_fill,
b65t_apparent_circle, b65t_loop_near_infty and b65t_pullback_transport. -/
theorem b65x_apparent_kernel (x : b65s_regular)
    (κ : FundamentalGroup b65x_Down (b65x_phiMap x) →* b4b_Group)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hC : ∀ γ : Path (b65x_phiMap x) (b65x_phiMap x),
      b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
        C.val * b65r_operator (b4b_toMatrix (κ (FundamentalGroup.fromPath ⟦γ⟧))) *
          (C⁻¹).val)
    (η : Path x x)
    (hη : FundamentalGroup.map b65s_inclusion x
      (FundamentalGroup.fromPath ⟦η⟧) = 1) :
    κ (FundamentalGroup.map b65x_phiMap x
      (FundamentalGroup.fromPath ⟦η⟧)) = 1 :=
  b65x_apparent_kernel_aux x κ C hC η hη

example (x : b65s_regular)
    (κ : FundamentalGroup b65x_Down (b65x_phiMap x) →* b4b_Group)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hC : ∀ γ : Path (b65x_phiMap x) (b65x_phiMap x),
      b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
        C.val * b65r_operator (b4b_toMatrix (κ (FundamentalGroup.fromPath ⟦γ⟧))) *
          (C⁻¹).val)
    (η : Path x x)
    (hη : FundamentalGroup.map b65s_inclusion x
      (FundamentalGroup.fromPath ⟦η⟧) = 1) :
    κ (FundamentalGroup.map b65x_phiMap x
      (FundamentalGroup.fromPath ⟦η⟧)) = 1 :=
  b65x_apparent_kernel x κ C hC η hη

/-- The sphere marking: the downstairs cut marking descends to the sphere minus the genuine
branch points, uniquely, sends each certified slot lasso to its initial cut value, and carries
the pullback transport with the same conjugator.
Source: b65t_puncture_fill and b65t_pullback_transport; b65x_trace_crossings, b65x_cut_word and
b65x_raw_reduction; B65-BRAIDCERT REPORT §1.4 and §2. -/
theorem b65x_sphere_marking (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (g : Fin 3 → Path (b65x_phiMap x) (b65x_phiMap x))
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)])
    (κ : FundamentalGroup b65x_Down (b65x_phiMap x) →* b4b_Group)
    (hκ : ∀ j, κ (FundamentalGroup.fromPath ⟦g j⟧) = b65b_cut j)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hC : ∀ γ : Path (b65x_phiMap x) (b65x_phiMap x),
      b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
        C.val * b65r_operator (b4b_toMatrix (κ (FundamentalGroup.fromPath ⟦γ⟧))) *
          (C⁻¹).val) :
    ∃! ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
      (∀ η : Path x x,
        ρ (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧)) =
          κ (FundamentalGroup.map b65x_phiMap x (FundamentalGroup.fromPath ⟦η⟧))) ∧
      (∀ i, ρ (FundamentalGroup.map b65s_inclusion x
        (FundamentalGroup.fromPath ⟦δ i⟧)) = b65b_initial i) ∧
      ∀ η : Path x x,
        b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
          C.val * b65r_operator (b4b_toMatrix
            (ρ (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧)))) *
              (C⁻¹).val :=
  b65x_sphere_marking_aux x δ hδ g hg κ hκ C hC

example (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (g : Fin 3 → Path (b65x_phiMap x) (b65x_phiMap x))
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)])
    (κ : FundamentalGroup b65x_Down (b65x_phiMap x) →* b4b_Group)
    (hκ : ∀ j, κ (FundamentalGroup.fromPath ⟦g j⟧) = b65b_cut j)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hC : ∀ γ : Path (b65x_phiMap x) (b65x_phiMap x),
      b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
        C.val * b65r_operator (b4b_toMatrix (κ (FundamentalGroup.fromPath ⟦γ⟧))) *
          (C⁻¹).val) :
    ∃! ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
      (∀ η : Path x x,
        ρ (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧)) =
          κ (FundamentalGroup.map b65x_phiMap x (FundamentalGroup.fromPath ⟦η⟧))) ∧
      (∀ i, ρ (FundamentalGroup.map b65s_inclusion x
        (FundamentalGroup.fromPath ⟦δ i⟧)) = b65b_initial i) ∧
      ∀ η : Path x x,
        b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
          C.val * b65r_operator (b4b_toMatrix
            (ρ (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧)))) *
              (C⁻¹).val :=
  b65x_sphere_marking x δ hδ g hg κ hκ C hC

/-- Lassos along the certified configuration path: each slot lasso extends to a based family
that avoids the moving configuration and infinity at every time.
Source: Birman, Braids, Links and Mapping Class Groups, §1.4 (isotopy extension);
B65-BRAIDCERT REPORT §1.2, checkers B, C and F. -/
theorem b65x_moving_lasso (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ),
      (∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ)) ∧
      (∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
        K i (t, 1) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
        ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ)) :=
  b65x_moving_lasso_aux p hp

example (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ),
      (∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ)) ∧
      (∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
        K i (t, 1) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
        ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ)) :=
  b65x_moving_lasso p hp

/-- The end of a based family avoiding the configuration is a loop of the sphere punctured at
the marks of `mr_base`, since the configuration ends at `mr_marks`.
Source: b65x_final_marks; b65b_vertex1 and b6_branch. -/
theorem b65x_final_loops (p : Fin 12 → ℂ)
    (K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ))
    (hKb : ∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
      K i (t, 1) = (mr_basePoint : OnePoint ℂ))
    (hKa : ∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
      ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ)) :
    ∃ κ₁ : Fin 13 → Path b63gP_basePoint b63gP_basePoint,
      ∀ i s, (κ₁ i s : OnePoint ℂ) = K i (1, s) :=
  b65x_final_loops_aux p K hKb hKa

example (p : Fin 12 → ℂ)
    (K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ))
    (hKb : ∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
      K i (t, 1) = (mr_basePoint : OnePoint ℂ))
    (hKa : ∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
      ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ)) :
    ∃ κ₁ : Fin 13 → Path b63gP_basePoint b63gP_basePoint,
      ∀ i s, (κ₁ i s : OnePoint ℂ) = K i (1, s) :=
  b65x_final_loops p K hKb hKa

/-- The two collinearity events of the certified path, both with p10 farther from the base
point, induce the positive moves 3 then 2: the explicit `mr_curve` classes are the move images
of the transported slot classes.
Source: B65-BRAIDCERT REPORT §1.3 rule [D] and §1.4; checkers C and F; Völklein, Groups as Galois
Groups, Ch. 10. -/
theorem b65x_event_moves (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ))
    (hK0 : ∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ))
    (hKb : ∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
      K i (t, 1) = (mr_basePoint : OnePoint ℂ))
    (hKa : ∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
      ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ))
    (κ₁ : Fin 13 → Path b63gP_basePoint b63gP_basePoint)
    (hκ₁ : ∀ i s, (κ₁ i s : OnePoint ℂ) = K i (1, s))
    (χ : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint →* b4b_Group)
    (i : Fin 13) :
    χ (b63gP_loops i.rev) =
      b65s_word b65b_pathWord (fun j ↦ χ (FundamentalGroup.fromPath ⟦κ₁ j⟧)) i :=
  b65x_event_moves_aux p hp K hK0 hKb hKa κ₁ hκ₁ χ i

example (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ))
    (hK0 : ∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ))
    (hKb : ∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
      K i (t, 1) = (mr_basePoint : OnePoint ℂ))
    (hKa : ∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
      ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ))
    (κ₁ : Fin 13 → Path b63gP_basePoint b63gP_basePoint)
    (hκ₁ : ∀ i s, (κ₁ i s : OnePoint ℂ) = K i (1, s))
    (χ : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint →* b4b_Group)
    (i : Fin 13) :
    χ (b63gP_loops i.rev) =
      b65s_word b65b_pathWord (fun j ↦ χ (FundamentalGroup.fromPath ⟦κ₁ j⟧)) i :=
  b65x_event_moves p hp K hK0 hKb hKa κ₁ hκ₁ χ i

/-- The end homeomorphism of an ambient isotopy that follows the configuration: it carries the
pulled-back explicit curves to `mr_curve` and the slot lassos to the transported loops.
Source: Birman, Braids, Links and Mapping Class Groups, §1.4 (isotopy extension); Völklein,
Groups as Galois Groups, Ch. 10; B65-BRAIDCERT REPORT §1.2. -/
theorem b65x_isotopy_marking (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ))
    (hK0 : ∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ))
    (hKb : ∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
      K i (t, 1) = (mr_basePoint : OnePoint ℂ))
    (hKa : ∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
      ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ))
    (κ₁ : Fin 13 → Path b63gP_basePoint b63gP_basePoint)
    (hκ₁ : ∀ i s, (κ₁ i s : OnePoint ℂ) = K i (1, s)) :
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base, ∃ γ : Fin 13 → Path x x,
      (∀ i s, (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
      (∀ i s, (γ i s).val ≠ 3 ∧ (γ i s).val ≠ 1 ∧
        (γ i s).val ≠ -2 ∧ ((γ i s).val : OnePoint ℂ) ≠ OnePoint.infty) ∧
      ∀ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
        ∃ χ : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint →* b4b_Group,
          (∀ i, χ (b63gP_loops i) = ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦γ i⟧))) ∧
          ∀ j, χ (FundamentalGroup.fromPath ⟦κ₁ j⟧) = ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦δ j⟧)) :=
  b65x_isotopy_marking_aux x δ hδ p hp K hK0 hKb hKa κ₁ hκ₁

example (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ))
    (hK0 : ∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ))
    (hKb : ∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
      K i (t, 1) = (mr_basePoint : OnePoint ℂ))
    (hKa : ∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
      ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ))
    (κ₁ : Fin 13 → Path b63gP_basePoint b63gP_basePoint)
    (hκ₁ : ∀ i s, (κ₁ i s : OnePoint ℂ) = K i (1, s)) :
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base, ∃ γ : Fin 13 → Path x x,
      (∀ i s, (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
      (∀ i s, (γ i s).val ≠ 3 ∧ (γ i s).val ≠ 1 ∧
        (γ i s).val ≠ -2 ∧ ((γ i s).val : OnePoint ℂ) ≠ OnePoint.infty) ∧
      ∀ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
        ∃ χ : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint →* b4b_Group,
          (∀ i, χ (b63gP_loops i) = ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦γ i⟧))) ∧
          ∀ j, χ (FundamentalGroup.fromPath ⟦κ₁ j⟧) = ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦δ j⟧)) :=
  b65x_isotopy_marking x δ hδ p hp K hK0 hKb hKa κ₁ hκ₁

/-- Corrected path-lasso transport, with the slot permutation and without a straight
final-lasso equation; the root witness is a binder.
Source: docs/specs/BraidBridges.md, corrected consumers; b65x_moving_lasso, b65x_final_loops,
b65x_isotopy_marking and b65x_event_moves. -/
theorem b65b_path_lasso_transport (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ),
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base,
    ∃ γ : Fin 13 → Path x x,
      (∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ)) ∧
      (∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
        K i (t, 1) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
        ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ)) ∧
      (∀ i s, (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
      (∀ i s, (γ i s).val ≠ 3 ∧ (γ i s).val ≠ 1 ∧
        (γ i s).val ≠ -2 ∧ ((γ i s).val : OnePoint ℂ) ≠ OnePoint.infty) ∧
      (∀ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
        ∀ i, ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦γ i.rev⟧)) =
          b65s_word [.positive 3, .positive 2]
            (fun j ↦ ρ (FundamentalGroup.map b65s_inclusion x
              (FundamentalGroup.fromPath ⟦δ j⟧))) i) :=
  b65b_path_lasso_transport_aux x δ hδ p hp

example (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ),
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base,
    ∃ γ : Fin 13 → Path x x,
      (∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ)) ∧
      (∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
        K i (t, 1) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
        ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ)) ∧
      (∀ i s, (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
      (∀ i s, (γ i s).val ≠ 3 ∧ (γ i s).val ≠ 1 ∧
        (γ i s).val ≠ -2 ∧ ((γ i s).val : OnePoint ℂ) ≠ OnePoint.infty) ∧
      (∀ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
        ∀ i, ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦γ i.rev⟧)) =
          b65s_word [.positive 3, .positive 2]
            (fun j ↦ ρ (FundamentalGroup.map b65s_inclusion x
              (FundamentalGroup.fromPath ⟦δ j⟧))) i) :=
  b65b_path_lasso_transport x δ hδ p hp

/-- Corrected transported identification: the slot lassos carry the initial cut values,
the pulled-back explicit curves carry the final values, one conjugator relates every regular
transport to the marking, and the final tuple lies in the selected component. The root witness
is a binder.
Source: B65-BRAIDCERT REPORT §§1–2; b65x_sphere_marking, b65b_path_lasso_transport,
b65b_path_replay, b65b_literal_matrices and b65b_component. -/
theorem b65b_transported_identification (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ x : b65s_regular,
    ∃ δ : Fin 13 → Path x x,
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base,
    ∃ γ : Fin 13 → Path x x,
    ∃ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
    ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
      (∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s)) ∧
      (∀ i (s : unitInterval),
        (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
      (∀ i, ρ (FundamentalGroup.map b65s_inclusion x
        (FundamentalGroup.fromPath ⟦δ i⟧)) = b65b_initial i) ∧
      (∀ i, ρ (FundamentalGroup.map b65s_inclusion x
        (FundamentalGroup.fromPath ⟦γ i.rev⟧)) = b65b_final i) ∧
      (∀ η : Path x x,
        b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
          C.val * b65r_operator (b4b_toMatrix
            (ρ (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧)))) *
              (C⁻¹).val) ∧
      (∀ i, b65f_transport (Fin 4 → ℂ) b65r_pullback
          (fun t ↦ ((γ i.rev).extend t).val) =
        C.val * b65r_operator (b65b_decode (b65b_finalIntegral i)) * (C⁻¹).val) ∧
      b4_SameComponent b65s_columnRoot b65b_final :=
  b65b_transported_identification_aux p hp

example (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ x : b65s_regular,
    ∃ δ : Fin 13 → Path x x,
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base,
    ∃ γ : Fin 13 → Path x x,
    ∃ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
    ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
      (∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s)) ∧
      (∀ i (s : unitInterval),
        (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
      (∀ i, ρ (FundamentalGroup.map b65s_inclusion x
        (FundamentalGroup.fromPath ⟦δ i⟧)) = b65b_initial i) ∧
      (∀ i, ρ (FundamentalGroup.map b65s_inclusion x
        (FundamentalGroup.fromPath ⟦γ i.rev⟧)) = b65b_final i) ∧
      (∀ η : Path x x,
        b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
          C.val * b65r_operator (b4b_toMatrix
            (ρ (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧)))) *
              (C⁻¹).val) ∧
      (∀ i, b65f_transport (Fin 4 → ℂ) b65r_pullback
          (fun t ↦ ((γ i.rev).extend t).val) =
        C.val * b65r_operator (b65b_decode (b65b_finalIntegral i)) * (C⁻¹).val) ∧
      b4_SameComponent b65s_columnRoot b65b_final :=
  b65b_transported_identification p hp

/-- Chain check: the corrected path consumer from the four path stages, generically in the
base point, the slot lassos and the root witness.
Source: b65x_moving_lasso, b65x_final_loops, b65x_isotopy_marking and b65x_event_moves. -/
example (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ K : Fin 13 → C(unitInterval × unitInterval, OnePoint ℂ),
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base,
    ∃ γ : Fin 13 → Path x x,
      (∀ i s, K i (0, s) = (b65b_lasso (b65x_slot i) s : OnePoint ℂ)) ∧
      (∀ i t, K i (t, 0) = (mr_basePoint : OnePoint ℂ) ∧
        K i (t, 1) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ i t s, K i (t, s) ≠ OnePoint.infty ∧
        ∀ j, K i (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ)) ∧
      (∀ i s, (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
      (∀ i s, (γ i s).val ≠ 3 ∧ (γ i s).val ≠ 1 ∧
        (γ i s).val ≠ -2 ∧ ((γ i s).val : OnePoint ℂ) ≠ OnePoint.infty) ∧
      (∀ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
        ∀ i, ρ (FundamentalGroup.map b65s_inclusion x
            (FundamentalGroup.fromPath ⟦γ i.rev⟧)) =
          b65s_word [.positive 3, .positive 2]
            (fun j ↦ ρ (FundamentalGroup.map b65s_inclusion x
              (FundamentalGroup.fromPath ⟦δ j⟧))) i) := by
  obtain ⟨K, hK0, hKb, hKa⟩ := b65x_moving_lasso p hp
  obtain ⟨κ₁, hκ₁⟩ := b65x_final_loops p K hKb hKa
  obtain ⟨h, γ, htrace, hsrc, hmark⟩ :=
    b65x_isotopy_marking x δ hδ p hp K hK0 hKb hKa κ₁ hκ₁
  refine ⟨K, h, γ, hK0, hKb, hKa, htrace, hsrc, fun ρ i ↦ ?_⟩
  obtain ⟨χ, hχγ, hχκ⟩ := hmark ρ
  rw [← hχγ, b65x_event_moves p hp K hK0 hKb hKa κ₁ hκ₁ χ i]
  change b65s_word b65b_pathWord _ i = b65s_word b65b_pathWord _ i
  congr 1
  funext j
  exact hχκ j

/-- Chain check: the conclusions of the corrected transported identification from the sphere
marking and the corrected path consumer, generically in the downstairs marking data.
Source: b65x_sphere_marking, b65b_path_lasso_transport, b65b_path_replay,
b65b_literal_matrices and b65b_component. -/
example (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (g : Fin 3 → Path (b65x_phiMap x) (b65x_phiMap x))
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)])
    (κ : FundamentalGroup b65x_Down (b65x_phiMap x) →* b4b_Group)
    (hκ : ∀ j, κ (FundamentalGroup.fromPath ⟦g j⟧) = b65b_cut j)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hC : ∀ γ : Path (b65x_phiMap x) (b65x_phiMap x),
      b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
        C.val * b65r_operator (b4b_toMatrix (κ (FundamentalGroup.fromPath ⟦γ⟧))) *
          (C⁻¹).val) :
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base,
    ∃ γ : Fin 13 → Path x x,
    ∃ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
      (∀ i (s : unitInterval),
        (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
      (∀ i, ρ (FundamentalGroup.map b65s_inclusion x
        (FundamentalGroup.fromPath ⟦δ i⟧)) = b65b_initial i) ∧
      (∀ i, ρ (FundamentalGroup.map b65s_inclusion x
        (FundamentalGroup.fromPath ⟦γ i.rev⟧)) = b65b_final i) ∧
      (∀ η : Path x x,
        b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
          C.val * b65r_operator (b4b_toMatrix
            (ρ (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧)))) *
              (C⁻¹).val) ∧
      (∀ i, b65f_transport (Fin 4 → ℂ) b65r_pullback
          (fun t ↦ ((γ i.rev).extend t).val) =
        C.val * b65r_operator (b65b_decode (b65b_finalIntegral i)) * (C⁻¹).val) ∧
      b4_SameComponent b65s_columnRoot b65b_final := by
  obtain ⟨ρ, ⟨-, hinit, htr⟩, -⟩ := b65x_sphere_marking x δ hδ g hg κ hκ C hC
  obtain ⟨K, h, γ, -, -, -, htrace, -, hmove⟩ := b65b_path_lasso_transport x δ hδ p hp
  have hvals : (fun j ↦ ρ (FundamentalGroup.map b65s_inclusion x
      (FundamentalGroup.fromPath ⟦δ j⟧))) = b65b_initial := funext hinit
  have hfin : ∀ i, ρ (FundamentalGroup.map b65s_inclusion x
      (FundamentalGroup.fromPath ⟦γ i.rev⟧)) = b65b_final i := by
    intro i
    rw [hmove ρ i, hvals]
    exact congrFun b65b_path_replay i
  refine ⟨h, γ, ρ, htrace, hinit, hfin, htr, fun i ↦ ?_, b65b_component⟩
  rw [htr, hfin, b65b_literal_matrices.2 i]

/-- Non-vacuity of the downstairs binders of `b65x_sphere_marking`: at the base point of any
column trace family, once-crossing generators, a cut marking and one conjugator exist. The
base point is off the cuts because a crossing word has only interior crossing times.
Source: b65x_trace_crossings, b65x_cut_generators and b65x_downstairs_marking. -/
example (x : b65s_regular) (δc : Fin 13 → Path x x)
    (hδc : ∀ i s, (δc i s).val = b65b_inverseNormalization (b65b_lasso i s)) :
    ∃ g : Fin 3 → Path (b65x_phiMap x) (b65x_phiMap x),
      (∀ j, b65x_CrossesAs (g j) [(j, 1)]) ∧
      ∃ κ : FundamentalGroup b65x_Down (b65x_phiMap x) →* b4b_Group,
        (∀ j, κ (FundamentalGroup.fromPath ⟦g j⟧) = b65b_cut j) ∧
        ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
          ∀ γ : Path (b65x_phiMap x) (b65x_phiMap x),
            b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
              C.val * b65r_operator (b4b_toMatrix (κ (FundamentalGroup.fromPath ⟦γ⟧))) *
                (C⁻¹).val := by
  have hy : ∀ k, ¬ b65x_OnCut k (b65x_phiMap x).val := by
    intro k hk
    obtain ⟨u, -, hpos, -, hcut, -⟩ := b65x_trace_crossings x δc hδc 0
    have h0 : (δc 0).map b65x_phiMap.continuous 0 = b65x_phiMap x := Path.source _
    obtain ⟨m, -, hm⟩ := (hcut k 0).1 (by rw [h0]; exact hk)
    have hu := (hpos m).1
    rw [← hm] at hu
    simp at hu
  obtain ⟨g, hg⟩ := b65x_cut_generators _ hy
  obtain ⟨κ, hκ, C, hC⟩ := b65x_downstairs_marking _ g hg
  exact ⟨g, hg, κ, hκ, C, hC⟩

/-- The corrected transported identification implies the archived conclusion of statement 8 of
docs/specs/BraidCertificate.md, given a root witness.
Source: docs/specs/BraidCertificate.md, set-aside section. -/
example (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ x : b65s_regular,
      ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base,
      ∃ γ : Fin 13 → Path x x,
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        (∀ i (s : unitInterval),
          (h (b65s_inclusion (γ i s)) : OnePoint ℂ) = mr_curve i s) ∧
        (∀ i, b65f_transport (Fin 4 → ℂ) b65r_pullback
            (fun t ↦ ((γ i.rev).extend t).val) =
          C.val * b65r_operator (b65b_decode (b65b_finalIntegral i)) * (C⁻¹).val) ∧
        b4_SameComponent b65s_columnRoot b65b_final := by
  obtain ⟨x, -, h, γ, -, C, -, htrace, -, -, -, hγ, hcomp⟩ :=
    b65b_transported_identification p hp
  exact ⟨x, h, γ, C, htrace, hγ, hcomp⟩

end HodgeLean.Foundations.Program
