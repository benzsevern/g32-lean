import Mathlib

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rex`: exact arithmetic for the G32 order certificate

Eisenstein integers `a + b ω` (`ω² = -1 - ω`) as pairs of integers, `4 × 4` matrices over them,
and the Boolean checks of a stabilizer-chain certificate: products `s t = t' u` with witnesses,
derivations of transversal elements from generators, and fixed columns.
HC no distance; AV milestone no distance.
-/

open scoped Pointwise

namespace HodgeLean.Foundations.Program

/-- **Eisenstein integers** `re + om · ω`, with `ω² = -1 - ω`, as pairs of integers.
Source: Ireland–Rosen, *A Classical Introduction to Modern Number Theory*, GTM 84, §1.4
(the ring `ℤ[ω]`). -/
@[ext] structure HurwitzPrymRex_Zw where
  re : ℤ
  om : ℤ
deriving DecidableEq

example : (⟨1, 0⟩ : HurwitzPrymRex_Zw) ≠ ⟨0, 1⟩ := by decide

namespace HurwitzPrymRex_Zw

/-- Addition in `ℤ[ω]`.
Source: Ireland–Rosen, GTM 84, §1.4. -/
def add (x y : HurwitzPrymRex_Zw) : HurwitzPrymRex_Zw := ⟨x.re + y.re, x.om + y.om⟩

example : add ⟨1, 2⟩ ⟨3, 4⟩ = ⟨4, 6⟩ := rfl

/-- Multiplication in `ℤ[ω]`: `(a + bω)(c + dω) = (ac - bd) + (ad + bc - bd)ω`.
Source: Ireland–Rosen, GTM 84, §1.4. -/
def mul (x y : HurwitzPrymRex_Zw) : HurwitzPrymRex_Zw :=
  ⟨x.re * y.re - x.om * y.om, x.re * y.om + x.om * y.re - x.om * y.om⟩

example : mul ⟨0, 1⟩ ⟨0, 1⟩ = ⟨-1, -1⟩ := rfl

end HurwitzPrymRex_Zw

/-- A literal `a + b ω`.
Source: Ireland–Rosen, GTM 84, §1.4. -/
abbrev z (a b : ℤ) : HurwitzPrymRex_Zw := ⟨a, b⟩

example : z 1 0 = ⟨1, 0⟩ := rfl

/-- `4 × 4` matrices over `ℤ[ω]`, as plain functions.
Source: Ireland–Rosen, GTM 84, §1.4. -/
abbrev HurwitzPrymRex_Mat := Fin 4 → Fin 4 → HurwitzPrymRex_Zw

open HurwitzPrymRex_Zw in
/-- The matrix product, written out.
Source: the definition of the matrix product. -/
def HurwitzPrymRex_mmul (A B : HurwitzPrymRex_Mat) : HurwitzPrymRex_Mat := fun i j ↦
  add (add (mul (A i 0) (B 0 j)) (mul (A i 1) (B 1 j)))
    (add (mul (A i 2) (B 2 j)) (mul (A i 3) (B 3 j)))

/-- Entrywise Boolean equality.
Source: the definition of matrix equality. -/
def HurwitzPrymRex_mbeq (A B : HurwitzPrymRex_Mat) : Bool :=
  (A 0 0 == B 0 0 && A 0 1 == B 0 1 && A 0 2 == B 0 2 && A 0 3 == B 0 3) &&
  (A 1 0 == B 1 0 && A 1 1 == B 1 1 && A 1 2 == B 1 2 && A 1 3 == B 1 3) &&
  (A 2 0 == B 2 0 && A 2 1 == B 2 1 && A 2 2 == B 2 2 && A 2 3 == B 2 3) &&
  (A 3 0 == B 3 0 && A 3 1 == B 3 1 && A 3 2 == B 3 2 && A 3 3 == B 3 3)

/-- The identity matrix.
Source: the definition of the identity matrix. -/
def HurwitzPrymRex_mone : HurwitzPrymRex_Mat := fun i j ↦ if i = j then z 1 0 else z 0 0

example : HurwitzPrymRex_mbeq HurwitzPrymRex_mone HurwitzPrymRex_mone = true := by decide

example : HurwitzPrymRex_mbeq (HurwitzPrymRex_mmul HurwitzPrymRex_mone HurwitzPrymRex_mone)
    HurwitzPrymRex_mone = true := by decide

/-- List lookup with a default.
Source: `List.getD`. -/
def HurwitzPrymRex_nth (L : List HurwitzPrymRex_Mat) : ℕ → HurwitzPrymRex_Mat
  | n => L.getD n HurwitzPrymRex_mone

example : HurwitzPrymRex_nth [] 3 = HurwitzPrymRex_mone := rfl

/-! ## The Boolean checks -/

/-- The product of one chosen element of each later level, `T₂[a₂] ⋯ T_k[a_k]`.
Source: Seress, *Permutation Group Algorithms*, Cambridge Tracts 152, §4.1 (sifting through a
stabilizer chain). -/
def HurwitzPrymRex_prodRest : List (List HurwitzPrymRex_Mat) → List ℕ → Option HurwitzPrymRex_Mat
  | [], [] => some HurwitzPrymRex_mone
  | T :: Ts, a :: as => if a < T.length then
      (HurwitzPrymRex_prodRest Ts as).map (HurwitzPrymRex_mmul (HurwitzPrymRex_nth T a)) else none
  | _, _ => none

example : HurwitzPrymRex_prodRest [] [] = some HurwitzPrymRex_mone := rfl

/-- One row of the Schreier check: for each `t`, `s t = T[j] u` with `u` from the witnesses.
Source: Seress, Cambridge Tracts 152, §4.1 (Schreier generators sift to the identity). -/
def HurwitzPrymRex_stepRow (s : HurwitzPrymRex_Mat) (T : List HurwitzPrymRex_Mat)
    (Ts : List (List HurwitzPrymRex_Mat)) : List HurwitzPrymRex_Mat → List (List ℕ) → Bool
  | [], [] => true
  | t :: ts, (j :: w) :: ws =>
      (decide (j < T.length) && match HurwitzPrymRex_prodRest Ts w with
        | some u => HurwitzPrymRex_mbeq (HurwitzPrymRex_mmul s t)
            (HurwitzPrymRex_mmul (HurwitzPrymRex_nth T j) u)
        | none => false) && HurwitzPrymRex_stepRow s T Ts ts ws
  | _, _ => false

example (s : HurwitzPrymRex_Mat) : HurwitzPrymRex_stepRow s [] [] [] [] = true := rfl

/-- The Schreier check of one level, row by row over the generators.
Source: Seress, Cambridge Tracts 152, §4.1. -/
def HurwitzPrymRex_stepCheck (T : List HurwitzPrymRex_Mat) (Ts : List (List HurwitzPrymRex_Mat)) :
    List HurwitzPrymRex_Mat → List (List (List ℕ)) → Bool
  | [], [] => true
  | s :: ss, r :: rs => HurwitzPrymRex_stepRow s T Ts T r && HurwitzPrymRex_stepCheck T Ts ss rs
  | _, _ => false

example : HurwitzPrymRex_stepCheck [] [] [] [] = true := rfl

/-- A derivation: `L[0] = 1` and each later `L[n]` is `S[a] L[p]` with `p < n`.
Source: Seress, Cambridge Tracts 152, §4.1 (Schreier trees). -/
def HurwitzPrymRex_derivCheck (S L : List HurwitzPrymRex_Mat) (W : List (ℕ × ℕ)) : Bool :=
  (List.range L.length).all fun n ↦
    if n = 0 then HurwitzPrymRex_mbeq (HurwitzPrymRex_nth L 0) HurwitzPrymRex_mone
    else decide ((W.getD (n - 1) (0, 0)).1 < S.length) && decide ((W.getD (n - 1) (0, 0)).2 < n) &&
      HurwitzPrymRex_mbeq (HurwitzPrymRex_nth L n)
        (HurwitzPrymRex_mmul (HurwitzPrymRex_nth S (W.getD (n - 1) (0, 0)).1)
          (HurwitzPrymRex_nth L (W.getD (n - 1) (0, 0)).2))

example : HurwitzPrymRex_derivCheck [] [HurwitzPrymRex_mone] [] = true := by decide

/-- The column `b` of a matrix.
Source: the definition of a matrix column. -/
def HurwitzPrymRex_colKey (b : Fin 4) (A : HurwitzPrymRex_Mat) : List HurwitzPrymRex_Zw :=
  [A 0 b, A 1 b, A 2 b, A 3 b]

example : HurwitzPrymRex_colKey 0 HurwitzPrymRex_mone = [z 1 0, z 0 0, z 0 0, z 0 0] := by decide

/-- Every matrix of `S` fixes the basis vector `e_b`.
Source: Seress, Cambridge Tracts 152, §4.1 (pointwise stabilizers). -/
def HurwitzPrymRex_fixCheck (b : Fin 4) (S : List HurwitzPrymRex_Mat) : Bool :=
  S.all fun s ↦ HurwitzPrymRex_colKey b s == HurwitzPrymRex_colKey b HurwitzPrymRex_mone

example : HurwitzPrymRex_fixCheck 0 [HurwitzPrymRex_mone] = true := by decide

/-- Each matrix of `S` has the two-sided inverse listed beside it.
Source: the definition of an invertible matrix. -/
def HurwitzPrymRex_invCheck : List HurwitzPrymRex_Mat → List HurwitzPrymRex_Mat → Bool
  | [], [] => true
  | s :: ss, s' :: ss' => HurwitzPrymRex_mbeq (HurwitzPrymRex_mmul s s') HurwitzPrymRex_mone &&
      HurwitzPrymRex_mbeq (HurwitzPrymRex_mmul s' s) HurwitzPrymRex_mone &&
      HurwitzPrymRex_invCheck ss ss'
  | _, _ => false

example : HurwitzPrymRex_invCheck [] [] = true := rfl

/-! ## Soundness of the checks -/

theorem HurwitzPrymRex_mbeq_sound {A B : HurwitzPrymRex_Mat} (h : HurwitzPrymRex_mbeq A B = true) :
    A = B := by
  simp only [HurwitzPrymRex_mbeq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h00, h01⟩, h02⟩, h03⟩, ⟨⟨⟨h10, h11⟩, h12⟩, h13⟩⟩, ⟨⟨⟨h20, h21⟩, h22⟩, h23⟩⟩,
    ⟨⟨⟨h30, h31⟩, h32⟩, h33⟩⟩ := h
  funext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem HurwitzPrymRex_nth_mem {L : List HurwitzPrymRex_Mat} {n : ℕ} (hn : n < L.length) :
    HurwitzPrymRex_nth L n ∈ L := by
  simp only [HurwitzPrymRex_nth, List.getD_eq_getElem _ _ hn]
  exact List.getElem_mem hn

theorem HurwitzPrymRex_stepRow_sound {s : HurwitzPrymRex_Mat} {T : List HurwitzPrymRex_Mat}
    {Ts : List (List HurwitzPrymRex_Mat)} {ts : List HurwitzPrymRex_Mat} {ws : List (List ℕ)}
    (h : HurwitzPrymRex_stepRow s T Ts ts ws = true) :
    ∀ t ∈ ts, ∃ t' ∈ T, ∃ w u, HurwitzPrymRex_prodRest Ts w = some u ∧
      HurwitzPrymRex_mmul s t = HurwitzPrymRex_mmul t' u := by
  induction ts generalizing ws with
  | nil => simp
  | cons t ts ih =>
    match ws, h with
    | (j :: w) :: ws, h =>
      simp only [HurwitzPrymRex_stepRow, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hj, hu⟩, hrest⟩ := h
      intro t' ht'
      rcases List.mem_cons.1 ht' with rfl | ht'
      · refine ⟨_, HurwitzPrymRex_nth_mem hj, w, ?_⟩
        revert hu
        cases HurwitzPrymRex_prodRest Ts w with
        | none => simp
        | some u => intro hu; exact ⟨u, rfl, HurwitzPrymRex_mbeq_sound hu⟩
      · exact ih hrest t' ht'

theorem HurwitzPrymRex_stepCheck_sound {T : List HurwitzPrymRex_Mat}
    {Ts : List (List HurwitzPrymRex_Mat)} {ss : List HurwitzPrymRex_Mat}
    {rs : List (List (List ℕ))} (h : HurwitzPrymRex_stepCheck T Ts ss rs = true) :
    ∀ s ∈ ss, ∀ t ∈ T, ∃ t' ∈ T, ∃ w u, HurwitzPrymRex_prodRest Ts w = some u ∧
      HurwitzPrymRex_mmul s t = HurwitzPrymRex_mmul t' u := by
  induction ss generalizing rs with
  | nil => simp
  | cons s ss ih =>
    match rs, h with
    | r :: rs, h =>
      simp only [HurwitzPrymRex_stepCheck, Bool.and_eq_true] at h
      intro s' hs'
      rcases List.mem_cons.1 hs' with rfl | hs'
      · exact HurwitzPrymRex_stepRow_sound h.1
      · exact ih h.2 s' hs'

theorem HurwitzPrymRex_derivCheck_spec {S L : List HurwitzPrymRex_Mat} {W : List (ℕ × ℕ)}
    (h : HurwitzPrymRex_derivCheck S L W = true) {n : ℕ} (hn : n < L.length) :
    (n = 0 ∧ HurwitzPrymRex_nth L 0 = HurwitzPrymRex_mone) ∨
      ∃ a p, a < S.length ∧ p < n ∧ HurwitzPrymRex_nth L n =
        HurwitzPrymRex_mmul (HurwitzPrymRex_nth S a) (HurwitzPrymRex_nth L p) := by
  simp only [HurwitzPrymRex_derivCheck, List.all_eq_true, List.mem_range] at h
  have hn' := h n hn
  split_ifs at hn' with h0
  · exact Or.inl ⟨h0, HurwitzPrymRex_mbeq_sound hn'⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hn'
    exact Or.inr ⟨_, _, hn'.1.1, hn'.1.2, HurwitzPrymRex_mbeq_sound hn'.2⟩

theorem HurwitzPrymRex_fixCheck_sound {b : Fin 4} {S : List HurwitzPrymRex_Mat}
    (h : HurwitzPrymRex_fixCheck b S = true) :
    ∀ s ∈ S, ∀ i, s i b = HurwitzPrymRex_mone i b := by
  simp only [HurwitzPrymRex_fixCheck, List.all_eq_true, beq_iff_eq] at h
  intro s hs i
  have := h s hs
  simp only [HurwitzPrymRex_colKey, List.cons.injEq] at this
  obtain ⟨h0, h1, h2, h3, -⟩ := this
  fin_cases i <;> assumption

theorem HurwitzPrymRex_invCheck_sound {S S' : List HurwitzPrymRex_Mat}
    (h : HurwitzPrymRex_invCheck S S' = true) :
    ∀ s ∈ S, ∃ s', HurwitzPrymRex_mmul s s' = HurwitzPrymRex_mone ∧
      HurwitzPrymRex_mmul s' s = HurwitzPrymRex_mone := by
  induction S generalizing S' with
  | nil => simp
  | cons s ss ih =>
    match S', h with
    | s' :: ss', h =>
      simp only [HurwitzPrymRex_invCheck, Bool.and_eq_true] at h
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨s', HurwitzPrymRex_mbeq_sound h.1.1, HurwitzPrymRex_mbeq_sound h.1.2⟩
      · exact ih h.2 x hx

/-! ## Evaluation in `ℂ` -/

section Eval

variable (w : ℂ)

/-- **Evaluation** `a + b ω ↦ a + b w` at a complex number `w`.
Source: Ireland–Rosen, GTM 84, §1.4. -/
noncomputable def HurwitzPrymRex_ev (x : HurwitzPrymRex_Zw) : ℂ := x.re + x.om * w

example : HurwitzPrymRex_ev w (z 1 0) = 1 := by simp [HurwitzPrymRex_ev]

/-- Entrywise evaluation of a matrix over `ℤ[ω]`.
Source: Ireland–Rosen, GTM 84, §1.4. -/
noncomputable def HurwitzPrymRex_evM (A : HurwitzPrymRex_Mat) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j ↦ HurwitzPrymRex_ev w (A i j)

example (A : HurwitzPrymRex_Mat) : HurwitzPrymRex_evM w A 0 0 = HurwitzPrymRex_ev w (A 0 0) := rfl

/-- The matrices of a list, evaluated, as a set.
Source: Ireland–Rosen, GTM 84, §1.4. -/
def HurwitzPrymRex_img (L : List HurwitzPrymRex_Mat) : Set (Matrix (Fin 4) (Fin 4) ℂ) :=
  {X | ∃ A ∈ L, HurwitzPrymRex_evM w A = X}

example : HurwitzPrymRex_img w [] = ∅ := by simp [HurwitzPrymRex_img]

/-- The products `t₁ ⋯ t_k` with `t_i` from the `i`-th list.
Source: Seress, Cambridge Tracts 152, §4.1 (the factorization through a stabilizer chain). -/
def HurwitzPrymRex_prodSet : List (List HurwitzPrymRex_Mat) → Set (Matrix (Fin 4) (Fin 4) ℂ)
  | [] => {1}
  | T :: Ts => HurwitzPrymRex_img w T * HurwitzPrymRex_prodSet Ts

example : HurwitzPrymRex_prodSet w [] = {1} := rfl

variable {w}

theorem HurwitzPrymRex_ev_add (x y : HurwitzPrymRex_Zw) :
    HurwitzPrymRex_ev w (HurwitzPrymRex_Zw.add x y) =
      HurwitzPrymRex_ev w x + HurwitzPrymRex_ev w y := by
  simp only [HurwitzPrymRex_ev, HurwitzPrymRex_Zw.add]
  push_cast
  ring

theorem HurwitzPrymRex_ev_mul (hw : w ^ 2 + w + 1 = 0) (x y : HurwitzPrymRex_Zw) :
    HurwitzPrymRex_ev w (HurwitzPrymRex_Zw.mul x y) =
      HurwitzPrymRex_ev w x * HurwitzPrymRex_ev w y := by
  simp only [HurwitzPrymRex_ev, HurwitzPrymRex_Zw.mul]
  push_cast
  linear_combination (-((x.om : ℂ) * y.om)) * hw

theorem HurwitzPrymRex_ev_injective (hw : w ^ 2 + w + 1 = 0) :
    Function.Injective (HurwitzPrymRex_ev w) := by
  intro x y h
  simp only [HurwitzPrymRex_ev] at h
  set e : ℤ := x.om - y.om with he
  set f : ℤ := x.re - y.re with hf
  have h0 : (f : ℂ) + e * w = 0 := by
    rw [he, hf]
    push_cast
    linear_combination h
  have h1 : ((f ^ 2 - f * e + e ^ 2 : ℤ) : ℂ) = 0 := by
    push_cast
    linear_combination ((f : ℂ) - e - e * w) * h0 + (e : ℂ) ^ 2 * hw
  have h2 : f ^ 2 - f * e + e ^ 2 = 0 := by exact_mod_cast h1
  have he0 : e = 0 := by nlinarith [sq_nonneg (2 * f - e), sq_nonneg e]
  have hf0 : f = 0 := by rw [he0] at h2; nlinarith [sq_nonneg f]
  ext <;> omega

theorem HurwitzPrymRex_evM_mmul (hw : w ^ 2 + w + 1 = 0) (A B : HurwitzPrymRex_Mat) :
    HurwitzPrymRex_evM w (HurwitzPrymRex_mmul A B) =
      HurwitzPrymRex_evM w A * HurwitzPrymRex_evM w B := by
  ext i j
  simp only [HurwitzPrymRex_evM, HurwitzPrymRex_mmul, Matrix.of_apply, Matrix.mul_apply,
    Fin.sum_univ_four, HurwitzPrymRex_ev_add, HurwitzPrymRex_ev_mul hw]
  ring

theorem HurwitzPrymRex_evM_mone : HurwitzPrymRex_evM w HurwitzPrymRex_mone = 1 := by
  ext i j
  simp only [HurwitzPrymRex_evM, HurwitzPrymRex_mone, Matrix.of_apply, Matrix.one_apply]
  split_ifs <;> simp [HurwitzPrymRex_ev]

theorem HurwitzPrymRex_evM_injective (hw : w ^ 2 + w + 1 = 0) :
    Function.Injective (HurwitzPrymRex_evM w) := by
  intro A B h
  funext i j
  exact HurwitzPrymRex_ev_injective hw (congrFun (congrFun h i) j)

theorem HurwitzPrymRex_prodRest_sound (hw : w ^ 2 + w + 1 = 0) :
    ∀ (Ts : List (List HurwitzPrymRex_Mat)) (as : List ℕ) (u : HurwitzPrymRex_Mat),
      HurwitzPrymRex_prodRest Ts as = some u → HurwitzPrymRex_evM w u ∈ HurwitzPrymRex_prodSet w Ts
  | [], [], u, h => by
    simp only [HurwitzPrymRex_prodRest, Option.some.injEq] at h
    subst h
    simp [HurwitzPrymRex_prodSet, HurwitzPrymRex_evM_mone]
  | T :: Ts, a :: as, u, h => by
    simp only [HurwitzPrymRex_prodRest] at h
    split_ifs at h with ha
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [HurwitzPrymRex_evM_mmul hw]
    exact Set.mul_mem_mul ⟨_, HurwitzPrymRex_nth_mem ha, rfl⟩
      (HurwitzPrymRex_prodRest_sound hw Ts as v hv)
  | [], _ :: _, u, h => by simp [HurwitzPrymRex_prodRest] at h
  | _ :: _, [], u, h => by simp [HurwitzPrymRex_prodRest] at h

/-- The Schreier check in `ℂ`. -/
theorem HurwitzPrymRex_stepCheck_eval (hw : w ^ 2 + w + 1 = 0) {T : List HurwitzPrymRex_Mat}
    {Ts : List (List HurwitzPrymRex_Mat)} {ss : List HurwitzPrymRex_Mat}
    {rs : List (List (List ℕ))} (h : HurwitzPrymRex_stepCheck T Ts ss rs = true) :
    ∀ s ∈ HurwitzPrymRex_img w ss, ∀ t ∈ HurwitzPrymRex_img w T, ∃ t' ∈ HurwitzPrymRex_img w T,
      ∃ u ∈ HurwitzPrymRex_prodSet w Ts, s * t = t' * u := by
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  obtain ⟨t', ht', a, u, hu, he⟩ := HurwitzPrymRex_stepCheck_sound h s hs t ht
  refine ⟨_, ⟨t', ht', rfl⟩, _, HurwitzPrymRex_prodRest_sound hw Ts a u hu, ?_⟩
  rw [← HurwitzPrymRex_evM_mmul hw, ← HurwitzPrymRex_evM_mmul hw, he]

/-- A derivation puts every listed matrix in the monoid generated by `S`. -/
theorem HurwitzPrymRex_derivCheck_eval (hw : w ^ 2 + w + 1 = 0) {S L : List HurwitzPrymRex_Mat}
    {W : List (ℕ × ℕ)} (h : HurwitzPrymRex_derivCheck S L W = true) :
    HurwitzPrymRex_img w L ⊆ Submonoid.closure (HurwitzPrymRex_img w S) := by
  have key : ∀ n, n < L.length →
      HurwitzPrymRex_evM w (HurwitzPrymRex_nth L n) ∈ Submonoid.closure (HurwitzPrymRex_img w S) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases HurwitzPrymRex_derivCheck_spec h hn with ⟨rfl, h0⟩ | ⟨a, p, ha, hp, he⟩
      · rw [h0, HurwitzPrymRex_evM_mone]
        exact one_mem _
      · rw [he, HurwitzPrymRex_evM_mmul hw]
        exact mul_mem (Submonoid.subset_closure ⟨_, HurwitzPrymRex_nth_mem ha, rfl⟩)
          (ih p hp (hp.trans hn))
  rintro _ ⟨A, hA, rfl⟩
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hA
  have := key n hn
  rwa [HurwitzPrymRex_nth, List.getD_eq_getElem _ _ hn] at this

/-- The first entry of a derivation is the identity. -/
theorem HurwitzPrymRex_derivCheck_one {S L : List HurwitzPrymRex_Mat} {W : List (ℕ × ℕ)}
    (h : HurwitzPrymRex_derivCheck S L W = true) (hL : 0 < L.length) :
    (1 : Matrix (Fin 4) (Fin 4) ℂ) ∈ HurwitzPrymRex_img w L := by
  rcases HurwitzPrymRex_derivCheck_spec h hL with ⟨-, h0⟩ | ⟨a, p, -, hp, -⟩
  · exact ⟨_, HurwitzPrymRex_nth_mem hL, by rw [h0, HurwitzPrymRex_evM_mone]⟩
  · exact absurd hp (Nat.not_lt_zero p)

theorem HurwitzPrymRex_fixCheck_eval {b : Fin 4} {S : List HurwitzPrymRex_Mat}
    (h : HurwitzPrymRex_fixCheck b S = true) :
    ∀ X ∈ HurwitzPrymRex_img w S, ∀ i, X i b = (1 : Matrix (Fin 4) (Fin 4) ℂ) i b := by
  rintro _ ⟨A, hA, rfl⟩ i
  rw [← HurwitzPrymRex_evM_mone (w := w)]
  simp only [HurwitzPrymRex_evM, Matrix.of_apply, HurwitzPrymRex_fixCheck_sound h A hA i]

theorem HurwitzPrymRex_invCheck_eval (hw : w ^ 2 + w + 1 = 0) {S S' : List HurwitzPrymRex_Mat}
    (h : HurwitzPrymRex_invCheck S S' = true) : ∀ X ∈ HurwitzPrymRex_img w S, IsUnit X := by
  rintro _ ⟨A, hA, rfl⟩
  obtain ⟨A', h1, h2⟩ := HurwitzPrymRex_invCheck_sound h A hA
  refine ⟨⟨HurwitzPrymRex_evM w A, HurwitzPrymRex_evM w A', ?_, ?_⟩, rfl⟩
  · rw [← HurwitzPrymRex_evM_mmul hw, h1, HurwitzPrymRex_evM_mone]
  · rw [← HurwitzPrymRex_evM_mmul hw, h2, HurwitzPrymRex_evM_mone]

/-- Distinct `b`-columns give distinct matrices with distinct `b`-columns, and count the list. -/
theorem HurwitzPrymRex_nodup_eval (hw : w ^ 2 + w + 1 = 0) {b : Fin 4}
    {T : List HurwitzPrymRex_Mat} (h : (T.map (HurwitzPrymRex_colKey b)).Nodup) :
    Set.InjOn (fun X : Matrix (Fin 4) (Fin 4) ℂ ↦ fun i ↦ X i b) (HurwitzPrymRex_img w T) ∧
      (HurwitzPrymRex_img w T).ncard = T.length := by
  have hkey : ∀ A B : HurwitzPrymRex_Mat,
      (fun i ↦ HurwitzPrymRex_evM w A i b) = (fun i ↦ HurwitzPrymRex_evM w B i b) →
        HurwitzPrymRex_colKey b A = HurwitzPrymRex_colKey b B := by
    intro A B hAB
    have hi : ∀ i, A i b = B i b := fun i ↦
      HurwitzPrymRex_ev_injective hw (congrFun hAB i)
    simp only [HurwitzPrymRex_colKey, hi]
  have hnd : (T.map fun A ↦ fun i ↦ HurwitzPrymRex_evM w A i b).Nodup := by
    rw [List.nodup_map_iff_inj_on (List.Nodup.of_map _ h)]
    intro A hA B hB hAB
    exact List.inj_on_of_nodup_map h hA hB (hkey A B hAB)
  have himg : HurwitzPrymRex_img w T = ((T.map (HurwitzPrymRex_evM w)).toFinset : Set _) := by
    ext X
    simp [HurwitzPrymRex_img]
  constructor
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hAB
    rw [List.inj_on_of_nodup_map hnd hA hB hAB]
  · rw [himg, Set.ncard_coe_finset, List.toFinset_card_of_nodup]
    · simp
    · have h' : ((T.map (HurwitzPrymRex_evM w)).map
          (fun X : Matrix (Fin 4) (Fin 4) ℂ ↦ fun i ↦ X i b)).Nodup := by
        rw [List.map_map]
        exact hnd
      exact h'.of_map _

end Eval

/-! ## The stabilizer chain in a monoid -/

section Chain

variable {M : Type*} [Monoid M]

/-- **One level of a stabilizer chain**: if `T` contains `1` and lies in `⟨S⟩`, the monoid `Q`
lies in `⟨S⟩`, and every `s t` (`s ∈ S`, `t ∈ T`) is `t' u` with `t' ∈ T`, `u ∈ Q`, then
`⟨S⟩ = T Q`.
Source: Seress, Cambridge Tracts 152, Lemma 4.2.1 (Schreier's lemma) and §4.1. -/
theorem HurwitzPrymRex_closure_eq_mul (S T : Set M) (Q : Submonoid M) (h1 : (1 : M) ∈ T)
    (hT : T ⊆ Submonoid.closure S) (hQ : Q ≤ Submonoid.closure S)
    (hstep : ∀ s ∈ S, ∀ t ∈ T, ∃ t' ∈ T, ∃ u ∈ Q, s * t = t' * u) :
    (Submonoid.closure S : Set M) = T * Q := by
  apply Set.Subset.antisymm
  · intro x hx
    induction hx using Submonoid.closure_induction_left with
    | one => exact ⟨1, h1, 1, Q.one_mem, one_mul 1⟩
    | mul_left s hs y _ ih =>
      obtain ⟨t, ht, q, hq, rfl⟩ := ih
      obtain ⟨t', ht', u, hu, he⟩ := hstep s hs t ht
      exact ⟨t', ht', u * q, Q.mul_mem hu hq, by rw [← mul_assoc, he, mul_assoc]⟩
  · rintro _ ⟨t, ht, q, hq, rfl⟩
    exact mul_mem (hT ht) (hQ hq)

/-- **Unique factorization** `x = t q` counts `T Q`. -/
theorem HurwitzPrymRex_ncard_mul (T Q : Set M)
    (hinj : ∀ t ∈ T, ∀ t' ∈ T, ∀ q ∈ Q, ∀ q' ∈ Q, t * q = t' * q' → t = t' ∧ q = q') :
    (T * Q).ncard = T.ncard * Q.ncard := by
  rw [← Set.image2_mul, ← Set.image_uncurry_prod, Set.InjOn.ncard_image, Set.ncard_prod]
  rintro ⟨t, q⟩ ⟨ht, hq⟩ ⟨t', q'⟩ ⟨ht', hq'⟩ h
  obtain ⟨rfl, rfl⟩ := hinj t ht t' ht' q hq q' hq' h
  rfl

end Chain

/-! ## Columns fixed by a monoid of matrices -/

section Fix

theorem HurwitzPrymRex_mul_col {b : Fin 4} (X Y : Matrix (Fin 4) (Fin 4) ℂ)
    (hY : ∀ i, Y i b = (1 : Matrix (Fin 4) (Fin 4) ℂ) i b) (i : Fin 4) : (X * Y) i b = X i b := by
  have : (X * Y) i b = (X * (1 : Matrix (Fin 4) (Fin 4) ℂ)) i b := by
    simp only [Matrix.mul_apply, hY]
  rw [this, Matrix.mul_one]

theorem HurwitzPrymRex_closure_fix {b : Fin 4} (S : Set (Matrix (Fin 4) (Fin 4) ℂ))
    (hS : ∀ X ∈ S, ∀ i, X i b = (1 : Matrix (Fin 4) (Fin 4) ℂ) i b) :
    ∀ Y ∈ Submonoid.closure S, ∀ i, Y i b = (1 : Matrix (Fin 4) (Fin 4) ℂ) i b := by
  intro Y hY
  induction hY using Submonoid.closure_induction_left with
  | one => exact fun _ ↦ rfl
  | mul_left X hX Y _ ih =>
    intro i
    rw [HurwitzPrymRex_mul_col X Y ih i]
    exact hS X hX i

theorem HurwitzPrymRex_closure_isUnit {M : Type*} [Monoid M] (S : Set M) (hS : ∀ X ∈ S, IsUnit X) :
    ∀ Y ∈ Submonoid.closure S, IsUnit Y := by
  intro Y hY
  induction hY using Submonoid.closure_induction_left with
  | one => exact isUnit_one
  | mul_left X hX Y _ ih => exact (hS X hX).mul ih

end Fix

end HodgeLean.Foundations.Program
