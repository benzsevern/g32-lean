import HodgeLean.Foundations.Program.G32PropFourSixArchiveWords

noncomputable section

open HodgeLean.Papers

namespace HodgeLean.Foundations.Program

def g32p_archiveReverseWords : Fin 4 → List (Fin 4) :=
  ![[0, 1, 1, 2, 2, 3, 2, 1, 0, 0],
    [0, 1, 1, 0, 0],
    [1, 1, 2, 1, 1, 3, 3, 0, 2, 3, 3, 0, 1, 1, 0],
    [0, 1, 0, 0, 3, 0, 0, 2, 2, 1, 3, 0, 2, 2, 1]]

def g32p_archiveIntegralWord : List (Fin 4) → HurwitzPrymRex_Mat
  | [] => HurwitzPrymRex_mone
  | i :: is => HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators i)
      (g32p_archiveIntegralWord is)

def g32p_archiveWordCertificate : List (Fin 4) → List HurwitzPrymRex_Mat → Bool
  | [], [a] => HurwitzPrymRex_mbeq a HurwitzPrymRex_mone
  | i :: is, a :: b :: rest =>
      HurwitzPrymRex_mbeq a (HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators i) b) &&
        g32p_archiveWordCertificate is (b :: rest)
  | _, _ => false

theorem g32p_archiveWordCertificate_sound (w : List (Fin 4))
    (stages : List HurwitzPrymRex_Mat)
    (h : g32p_archiveWordCertificate w stages = true) :
    ∃ a rest, stages = a :: rest ∧ g32p_archiveIntegralWord w = a := by
  induction w generalizing stages with
  | nil =>
      cases stages with
      | nil => simp [g32p_archiveWordCertificate] at h
      | cons a rest =>
          cases rest with
          | nil =>
              exact ⟨a, [], rfl, (HurwitzPrymRex_mbeq_sound h).symm⟩
          | cons b rest => simp [g32p_archiveWordCertificate] at h
  | cons i is ih =>
      cases stages with
      | nil => simp [g32p_archiveWordCertificate] at h
      | cons a rest =>
          cases rest with
          | nil => simp [g32p_archiveWordCertificate] at h
          | cons b rest =>
              simp only [g32p_archiveWordCertificate, Bool.and_eq_true] at h
              obtain ⟨c, tail, hc, hv⟩ := ih (b :: rest) h.2
              cases hc
              exact ⟨a, b :: rest, rfl, by
                rw [g32p_archiveIntegralWord, hv]
                exact (HurwitzPrymRex_mbeq_sound h.1).symm⟩


def g32p_archiveReverseStages_0 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩],
    ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩],
    ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩],
    ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩],
    ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩],
    ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩],
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩],
    ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩],
    ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
    ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩],
    ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩],
    ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩],
    ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩],
    ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩],
    ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩],
    ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩],
    ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩],
    ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩],
    ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 400000 in
theorem g32p_archiveReverseCertificate_0 :
    g32p_archiveWordCertificate (g32p_archiveReverseWords 0)
      g32p_archiveReverseStages_0 = true := by
  decide +kernel

theorem g32p_archiveReverseIntegral_0 :
    g32p_archiveIntegralWord (g32p_archiveReverseWords 0) =
      HurwitzPrymRex_nth HurwitzPrymRex_g32SOne 0 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_archiveReverseCertificate_0
  have ha : a = g32p_archiveReverseStages_0.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  decide +kernel

def g32p_archiveReverseStages_1 : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩],
    ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩],
    ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩],
    ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩],
    ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩],
    ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩],
    ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩],
    ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 400000 in
theorem g32p_archiveReverseCertificate_1 :
    g32p_archiveWordCertificate (g32p_archiveReverseWords 1)
      g32p_archiveReverseStages_1 = true := by
  decide +kernel

theorem g32p_archiveReverseIntegral_1 :
    g32p_archiveIntegralWord (g32p_archiveReverseWords 1) =
      HurwitzPrymRex_nth HurwitzPrymRex_g32SOne 1 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_archiveReverseCertificate_1
  have ha : a = g32p_archiveReverseStages_1.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  decide +kernel

def g32p_archiveReverseStages_2 : List HurwitzPrymRex_Mat :=
  [![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩],
    ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]],
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩],
    ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩],
    ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]],
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩],
    ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩],
    ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]],
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩],
    ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩],
    ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩],
    ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩],
    ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩],
    ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩],
    ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩],
    ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩],
    ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩],
    ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩],
    ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩],
    ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]],
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩],
    ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩],
    ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩],
    ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩],
    ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩],
    ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩],
    ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩],
    ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩],
    ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩],
    ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩],
    ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩],
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩],
    ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩],
    ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩],
    ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩],
    ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩],
    ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩],
    ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 400000 in
theorem g32p_archiveReverseCertificate_2 :
    g32p_archiveWordCertificate (g32p_archiveReverseWords 2)
      g32p_archiveReverseStages_2 = true := by
  decide +kernel

theorem g32p_archiveReverseIntegral_2 :
    g32p_archiveIntegralWord (g32p_archiveReverseWords 2) =
      HurwitzPrymRex_nth HurwitzPrymRex_g32SOne 2 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_archiveReverseCertificate_2
  have ha : a = g32p_archiveReverseStages_2.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  decide +kernel

def g32p_archiveReverseStages_3 : List HurwitzPrymRex_Mat :=
  [![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩],
    ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩],
    ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩],
    ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]],
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩],
    ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩],
    ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩],
    ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩],
    ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩],
    ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩],
    ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 0⟩],
    ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩],
    ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩],
    ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩],
    ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩],
    ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩],
    ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩],
    ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩],
    ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩],
    ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩],
    ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩],
    ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩],
    ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩],
    ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩],
    ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩],
    ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩],
    ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩],
    ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩],
    ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩],
    ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩],
    ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩],
    ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩],
    ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩],
    ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩],
    ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩],
    ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩],
    ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩],
    ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 400000 in
theorem g32p_archiveReverseCertificate_3 :
    g32p_archiveWordCertificate (g32p_archiveReverseWords 3)
      g32p_archiveReverseStages_3 = true := by
  decide +kernel

theorem g32p_archiveReverseIntegral_3 :
    g32p_archiveIntegralWord (g32p_archiveReverseWords 3) =
      HurwitzPrymRex_nth HurwitzPrymRex_g32SOne 3 := by
  obtain ⟨a, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _
    g32p_archiveReverseCertificate_3
  have ha : a = g32p_archiveReverseStages_3.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, ha]
  decide +kernel


theorem g32p_archiveReverseIntegral (i : Fin 4) :
    g32p_archiveIntegralWord (g32p_archiveReverseWords i) =
      HurwitzPrymRex_nth HurwitzPrymRex_g32SOne i.val := by
  fin_cases i
  · exact g32p_archiveReverseIntegral_0
  · exact g32p_archiveReverseIntegral_1
  · exact g32p_archiveReverseIntegral_2
  · exact g32p_archiveReverseIntegral_3

def g32p_archiveWord (w : List (Fin 4)) : g32p_G :=
  (w.map (fun i => g32p_word (g32p_archiveWords i))).prod

theorem g32p_archiveIntegralWord_map (w : List (Fin 4)) :
    b4b_toMatrix (g32p_archiveWord w) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
        (g32p_archiveIntegralWord w)) := by
  induction w with
  | nil => simp only [g32p_archiveWord, List.map_nil, List.prod_nil, map_one,
      g32p_archiveIntegralWord, HurwitzPrymRex_evM_mone]
  | cons i is ih =>
      change b4b_toMatrix (g32p_word (g32p_archiveWords i) * g32p_archiveWord is) = _
      rw [map_mul, g32p_archiveIntegralWord, HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
        map_mul, ← ih, ← g32p_archiveWordIntegral, ← g32p_integralWord_map]

theorem g32p_archiveReverseWord (i : Fin 4) :
    g32p_archiveWord (g32p_archiveReverseWords i) = b4b_generators i := by
  apply Subtype.ext
  change b4b_toMatrix _ = b4b_toMatrix _
  rw [g32p_archiveIntegralWord_map, g32p_archiveReverseIntegral,
    g32p_integralGenerator_map]

theorem g32p_archiveWord_matrix_mem (w : List (Fin 4)) :
    b4b_toMatrix (g32p_archiveWord w) ∈
      Submonoid.closure (Set.range (fun i : Fin 4 =>
        (g32p_archiveGenerators i).submatrix g32p_archiveCoordinates g32p_archiveCoordinates)) := by
  induction w with
  | nil => exact Submonoid.one_mem _
  | cons i is ih =>
      change b4b_toMatrix (g32p_word (g32p_archiveWords i) * g32p_archiveWord is) ∈ _
      rw [map_mul, g32p_archiveGenerator_word]
      exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨i, rfl⟩) ih

theorem g32p_archive_matrix_closure :
    Submonoid.closure (Set.range (fun i : Fin 4 =>
      (g32p_archiveGenerators i).submatrix g32p_archiveCoordinates g32p_archiveCoordinates)) =
        g32h_G := by
  apply le_antisymm
  · apply Submonoid.closure_le.mpr
    rintro x ⟨i, rfl⟩
    change (g32p_archiveGenerators i).submatrix g32p_archiveCoordinates
      g32p_archiveCoordinates ∈ g32h_G
    rw [← g32p_archiveGenerator_word]
    exact (g32p_word (g32p_archiveWords i)).property
  · apply Submonoid.closure_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hg (i : Fin 4) := g32p_archiveWord_matrix_mem (g32p_archiveReverseWords i)
    simp only [g32p_archiveReverseWord] at hg
    rcases hx with rfl | rfl | rfl | rfl
    · exact hg 0
    · exact hg 1
    · exact hg 2
    · exact hg 3

end HodgeLean.Foundations.Program
