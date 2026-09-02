import Mathlib

/-!
# Ulam Problem 164: a fully formalized two-cluster counterexample

This file formalizes the counterexample in Section 6 of
"Solutions and Counterexamples to Six Problems from the Scottish Book".

We deliberately encode "nearest neighbors" order-theoretically: two distinct
points of a finite ordered set are adjacent iff there is no point of the set
strictly between them.  A permissible step from `p` goes to `T p` or to a
point adjacent to `T p`.
-/

namespace Ulam164

open Set

noncomputable section

/-- Two points of a finite ordered set are consecutive in its induced order. -/
def Adjacent (E : Finset ℝ) (x y : ℝ) : Prop :=
  x ∈ E ∧ y ∈ E ∧ x ≠ y ∧
    ∀ z ∈ E, ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x))

/-- A permissible one-step move in the literal formulation of Problem 164. -/
def PermissibleStep (E : Finset ℝ) (T : ℝ → ℝ) (p q : ℝ) : Prop :=
  p ∈ E ∧ q ∈ E ∧ (q = T p ∨ Adjacent E q (T p))

/-- Reachability by any finite number of permissible steps. -/
def Reachable (E : Finset ℝ) (T : ℝ → ℝ) (p q : ℝ) : Prop :=
  Relation.ReflTransGen (fun x y => PermissibleStep E T x y) p q

/-- `ReachableIn E T n p q` means that `q` is reached from `p` in exactly
`n` permissible steps.  This is the counted version needed to encode the
printed bound `⌊k / ε⌋`. -/
inductive ReachableIn (E : Finset ℝ) (T : ℝ → ℝ) : ℕ → ℝ → ℝ → Prop
  | zero (p : ℝ) : ReachableIn E T 0 p p
  | succ {n : ℕ} {p q r : ℝ} :
      ReachableIn E T n p q →
      PermissibleStep E T q r →
      ReachableIn E T (n + 1) p r

lemma ReachableIn.toReachable {E : Finset ℝ} {T : ℝ → ℝ}
    {n : ℕ} {p q : ℝ} (h : ReachableIn E T n p q) : Reachable E T p q := by
  induction h with
  | zero p => exact Relation.ReflTransGen.refl
  | succ hstep hlast ih =>
      exact Relation.ReflTransGen.tail ih hlast

/-- The hypotheses of the literal printed Problem 164 for one value of `ε`. -/
def Admissible (ε : ℝ) (E : Finset ℝ) (T : ℝ → ℝ) : Prop :=
  0 < ε ∧
  0 ∈ E ∧
  1 ∈ E ∧
  (∀ x ∈ E, x ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ p ∈ E, T p ∈ E ∧ ε < |p - T p|)

/-- Every starting point escapes by distance at least `1/3` in at most `N`
permissible steps. -/
def EscapesWithin (N : ℕ) (E : Finset ℝ) (T : ℝ → ℝ) : Prop :=
  ∀ p ∈ E, ∃ n : ℕ, n ≤ N ∧ ∃ q ∈ E,
    ReachableIn E T n p q ∧ (1 / 3 : ℝ) ≤ |q - p|

/-- The universal-constant assertion asked for in the literal formulation of
Problem 164.  The notation `⌊x⌋₊` is the natural-number floor. -/
def UniversalBound (k : ℝ) : Prop :=
  0 < k ∧
  ∀ ε : ℝ, ∀ E : Finset ℝ, ∀ T : ℝ → ℝ,
    Admissible ε E T → EscapesWithin ⌊k / ε⌋₊ E T

/-- The left seven-point cluster, with `δ = 2 ε`. -/
def C0 (ε : ℝ) : Finset ℝ :=
  (Finset.range 7).image (fun j : ℕ => (j : ℝ) * (2 * ε))

/-- The reflected right seven-point cluster. -/
def C1 (ε : ℝ) : Finset ℝ :=
  (Finset.range 7).image (fun j : ℕ => 1 - (j : ℝ) * (2 * ε))

/-- The full finite set. -/
def E (ε : ℝ) : Finset ℝ := C0 ε ∪ C1 ε

/-- The map `τ` on the left cluster.  On cluster points this is exactly
`jδ ↦ 5δ` for `j ≤ 3`, and `jδ ↦ δ` for `j ≥ 4`. -/
def τ (ε x : ℝ) : ℝ := if x ≤ 6 * ε then 10 * ε else 2 * ε

/-- The map `T`, equal to `τ` on the left cluster and its reflection on the right. -/
def T (ε x : ℝ) : ℝ :=
  if x < (1 / 2 : ℝ) then τ ε x else 1 - τ ε (1 - x)

lemma mem_C0_iff {ε x : ℝ} :
    x ∈ C0 ε ↔ ∃ j : ℕ, j < 7 ∧ x = (j : ℝ) * (2 * ε) := by
  classical
  simp only [C0, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩

lemma mem_C1_iff {ε x : ℝ} :
    x ∈ C1 ε ↔ ∃ j : ℕ, j < 7 ∧ x = 1 - (j : ℝ) * (2 * ε) := by
  classical
  simp only [C1, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩

lemma zero_mem_C0 (ε : ℝ) : 0 ∈ C0 ε := by
  rw [mem_C0_iff]
  exact ⟨0, by norm_num, by norm_num⟩

lemma one_mem_C1 (ε : ℝ) : 1 ∈ C1 ε := by
  rw [mem_C1_iff]
  exact ⟨0, by norm_num, by norm_num⟩

lemma zero_mem_E (ε : ℝ) : 0 ∈ E ε := by
  exact Finset.mem_union_left _ (zero_mem_C0 ε)

lemma one_mem_E (ε : ℝ) : 1 ∈ E ε := by
  exact Finset.mem_union_right _ (one_mem_C1 ε)

lemma C0_nonneg {ε x : ℝ} (hε : 0 < ε) (hx : x ∈ C0 ε) : 0 ≤ x := by
  rw [mem_C0_iff] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  positivity

lemma C0_upper {ε x : ℝ} (hε : 0 < ε) (hx : x ∈ C0 ε) : x ≤ 12 * ε := by
  rw [mem_C0_iff] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have hj6 : j ≤ 6 := by omega
  have hj6R : (j : ℝ) ≤ 6 := by exact_mod_cast hj6
  nlinarith

lemma C0_left_half {ε x : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 72) (hx : x ∈ C0 ε) :
    x < 1 / 2 := by
  have hu := C0_upper hε hx
  linarith

lemma C1_right_half {ε x : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 72) (hx : x ∈ C1 ε) :
    1 / 2 < x := by
  rw [mem_C1_iff] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have hj6 : j ≤ 6 := by omega
  have hj6R : (j : ℝ) ≤ 6 := by exact_mod_cast hj6
  nlinarith

lemma reflect_C1_mem_C0 {ε x : ℝ} (hx : x ∈ C1 ε) : 1 - x ∈ C0 ε := by
  rw [mem_C1_iff] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  rw [mem_C0_iff]
  exact ⟨j, hj, by ring⟩

lemma reflect_C0_mem_C1 {ε x : ℝ} (hx : x ∈ C0 ε) : 1 - x ∈ C1 ε := by
  rw [mem_C0_iff] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  rw [mem_C1_iff]
  exact ⟨j, hj, by ring⟩

lemma two_eps_mem_C0 (ε : ℝ) : 2 * ε ∈ C0 ε := by
  rw [mem_C0_iff]
  exact ⟨1, by norm_num, by norm_num⟩

lemma four_eps_mem_C0 (ε : ℝ) : 4 * ε ∈ C0 ε := by
  rw [mem_C0_iff]
  exact ⟨2, by norm_num, by ring⟩

lemma ten_eps_mem_C0 (ε : ℝ) : 10 * ε ∈ C0 ε := by
  rw [mem_C0_iff]
  exact ⟨5, by norm_num, by ring⟩

lemma twelve_eps_mem_C0 (ε : ℝ) : 12 * ε ∈ C0 ε := by
  rw [mem_C0_iff]
  exact ⟨6, by norm_num, by ring⟩

lemma tau_mem_C0 {ε x : ℝ} (_hx : x ∈ C0 ε) : τ ε x ∈ C0 ε := by
  simp only [τ]
  split_ifs
  · exact ten_eps_mem_C0 ε
  · exact two_eps_mem_C0 ε

lemma gap_after_six {ε x : ℝ} (hε : 0 < ε) (hx : x ∈ C0 ε) (h6 : 6 * ε < x) :
    8 * ε ≤ x := by
  rw [mem_C0_iff] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have hj4 : 4 ≤ j := by
    by_contra h
    have hj3 : j ≤ 3 := by omega
    have hj3R : (j : ℝ) ≤ 3 := by exact_mod_cast hj3
    nlinarith
  have hj4R : (4 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj4
  nlinarith

lemma displacement_tau {ε x : ℝ} (hε : 0 < ε) (hx : x ∈ C0 ε) :
    ε < |x - τ ε x| := by
  unfold τ
  by_cases h : x ≤ 6 * ε
  · simp [h]
    have : x ≤ 6 * ε := h
    have hnonneg : 0 ≤ 10 * ε - x := by nlinarith
    rw [abs_sub_comm, abs_of_nonneg hnonneg]
    linarith
  · have h6 : 6 * ε < x := lt_of_not_ge h
    have h8 : 8 * ε ≤ x := gap_after_six hε hx h6
    simp [h]
    have hnonneg : 0 ≤ x - 2 * ε := by nlinarith
    rw [abs_of_nonneg hnonneg]
    linarith

lemma T_eq_tau_on_C0 {ε x : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 72)
    (hx : x ∈ C0 ε) : T ε x = τ ε x := by
  unfold T
  rw [if_pos (C0_left_half hε hsmall hx)]

lemma T_eq_reflect_tau_on_C1 {ε x : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 72)
    (hx : x ∈ C1 ε) : T ε x = 1 - τ ε (1 - x) := by
  unfold T
  rw [if_neg (not_lt.mpr (le_of_lt (C1_right_half hε hsmall hx)))]

lemma T_mem_same_C0 {ε x : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 72)
    (hx : x ∈ C0 ε) : T ε x ∈ C0 ε := by
  rw [T_eq_tau_on_C0 hε hsmall hx]
  exact tau_mem_C0 hx

lemma T_mem_same_C1 {ε x : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 72)
    (hx : x ∈ C1 ε) : T ε x ∈ C1 ε := by
  rw [T_eq_reflect_tau_on_C1 hε hsmall hx]
  apply reflect_C0_mem_C1
  exact tau_mem_C0 (reflect_C1_mem_C0 hx)

lemma displacement_T_C0 {ε x : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 72)
    (hx : x ∈ C0 ε) : ε < |x - T ε x| := by
  rw [T_eq_tau_on_C0 hε hsmall hx]
  exact displacement_tau hε hx

lemma displacement_T_C1 {ε x : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 72)
    (hx : x ∈ C1 ε) : ε < |x - T ε x| := by
  rw [T_eq_reflect_tau_on_C1 hε hsmall hx]
  have h := displacement_tau hε (reflect_C1_mem_C0 hx)
  have heq : x - (1 - τ ε (1 - x)) = -((1 - x) - τ ε (1 - x)) := by ring
  rw [heq, abs_neg]
  exact h

lemma T_maps_E {ε x : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 72) (hx : x ∈ E ε) :
    T ε x ∈ E ε := by
  rw [E] at hx ⊢
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ (T_mem_same_C0 hε hsmall hx)
  · exact Finset.mem_union_right _ (T_mem_same_C1 hε hsmall hx)

lemma displacement_T {ε x : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 72) (hx : x ∈ E ε) :
    ε < |x - T ε x| := by
  rw [E] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact displacement_T_C0 hε hsmall hx
  · exact displacement_T_C1 hε hsmall hx

/-- Every constructed point lies in the unit interval, as required by the problem. -/
lemma E_subset_unit_interval {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 72) :
    ∀ x ∈ E ε, x ∈ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  rw [E] at hx
  rcases Finset.mem_union.mp hx with hx0 | hx1
  · have h0 := C0_nonneg hε hx0
    have hU := C0_upper hε hx0
    constructor
    · exact h0
    · linarith
  · have hr : 1 - x ∈ C0 ε := reflect_C1_mem_C0 hx1
    have h0 := C0_nonneg hε hr
    have hU := C0_upper hε hr
    constructor <;> linarith

/-- An adjacent point to either of the two possible `τ`-values cannot jump
across the large gap to the right cluster. -/
lemma adjacent_to_tau_stays_C0 {ε x y : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 72)
    (hx : x ∈ C0 ε) (hyE : y ∈ E ε) (hadj : Adjacent (E ε) y (τ ε x)) :
    y ∈ C0 ε := by
  rw [E] at hyE
  rcases Finset.mem_union.mp hyE with hy0 | hy1
  · exact hy0
  · exfalso
    have hyhalf : 1 / 2 < y := C1_right_half hε hsmall hy1
    have htau : τ ε x ∈ C0 ε := tau_mem_C0 hx
    have htauhalf : τ ε x < 1 / 2 := C0_left_half hε hsmall htau
    rcases hadj with ⟨hyE', htE, hne, hbetween⟩
    by_cases ht : τ ε x = 10 * ε
    · have hzE : 12 * ε ∈ E ε := by
        rw [E]
        exact Finset.mem_union_left _ (twelve_eps_mem_C0 ε)
      have hlt1 : τ ε x < 12 * ε := by rw [ht]; linarith
      have hlt2 : 12 * ε < y := by
        have : 12 * ε < 1 / 2 := by linarith
        linarith
      exact hbetween (12 * ε) hzE (Or.inr ⟨hlt1, hlt2⟩)
    · have ht2 : τ ε x = 2 * ε := by
        unfold τ at ht ⊢
        split_ifs at ht ⊢ <;> simp_all
      have hzE : 4 * ε ∈ E ε := by
        rw [E]
        exact Finset.mem_union_left _ (four_eps_mem_C0 ε)
      have hlt1 : τ ε x < 4 * ε := by rw [ht2]; linarith
      have h4half : 4 * ε < 1 / 2 := by linarith
      have hlt2 : 4 * ε < y := lt_trans h4half hyhalf
      exact hbetween (4 * ε) hzE (Or.inr ⟨hlt1, hlt2⟩)

/-- Reflection of adjacency. -/
lemma adjacent_reflect {ε x y : ℝ} (h : Adjacent (E ε) x y) :
    Adjacent (E ε) (1 - x) (1 - y) := by
  rcases h with ⟨hx, hy, hxy, hbetween⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [E] at hx ⊢
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_right _ (reflect_C0_mem_C1 hx)
    · exact Finset.mem_union_left _ (reflect_C1_mem_C0 hx)
  · rw [E] at hy ⊢
    rcases Finset.mem_union.mp hy with hy | hy
    · exact Finset.mem_union_right _ (reflect_C0_mem_C1 hy)
    · exact Finset.mem_union_left _ (reflect_C1_mem_C0 hy)
  · intro heq
    apply hxy
    linarith
  · intro z hz hbet
    have hz' : 1 - z ∈ E ε := by
      rw [E] at hz ⊢
      rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.mem_union_right _ (reflect_C0_mem_C1 hz)
      · exact Finset.mem_union_left _ (reflect_C1_mem_C0 hz)
    apply hbetween (1 - z) hz'
    rcases hbet with hbet | hbet
    · right; constructor <;> linarith
    · left; constructor <;> linarith

lemma permissible_from_C0_stays {ε p q : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 72)
    (hp : p ∈ C0 ε) (hstep : PermissibleStep (E ε) (T ε) p q) :
    q ∈ C0 ε := by
  rcases hstep with ⟨hpE, hqE, hq⟩
  rcases hq with rfl | hadj
  · exact T_mem_same_C0 hε hsmall hp
  · rw [T_eq_tau_on_C0 hε hsmall hp] at hadj
    exact adjacent_to_tau_stays_C0 hε hsmall hp hqE hadj

lemma permissible_from_C1_stays {ε p q : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 72)
    (hp : p ∈ C1 ε) (hstep : PermissibleStep (E ε) (T ε) p q) :
    q ∈ C1 ε := by
  rcases hstep with ⟨hpE, hqE, hq⟩
  rcases hq with rfl | hadj
  · exact T_mem_same_C1 hε hsmall hp
  · have hp0 : 1 - p ∈ C0 ε := reflect_C1_mem_C0 hp
    have hT : T ε p = 1 - τ ε (1 - p) := T_eq_reflect_tau_on_C1 hε hsmall hp
    rw [hT] at hadj
    have hadj' : Adjacent (E ε) (1 - q) (1 - (1 - τ ε (1 - p))) :=
      adjacent_reflect hadj
    have hreflect_tau : 1 - (1 - τ ε (1 - p)) = τ ε (1 - p) := by
      ring
    rw [hreflect_tau] at hadj'
    have hqE' : 1 - q ∈ E ε := by
      rw [E] at hqE ⊢
      rcases Finset.mem_union.mp hqE with hq0 | hq1
      · exact Finset.mem_union_right _ (reflect_C0_mem_C1 hq0)
      · exact Finset.mem_union_left _ (reflect_C1_mem_C0 hq1)
    have hs : 1 - q ∈ C0 ε :=
      adjacent_to_tau_stays_C0 hε hsmall hp0 hqE' hadj'
    have hq1 := reflect_C0_mem_C1 hs
    simpa only [sub_sub_cancel] using hq1

lemma reachable_from_C0_stays {ε p q : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 72)
    (hp : p ∈ C0 ε) (hr : Reachable (E ε) (T ε) p q) :
    q ∈ C0 ε := by
  induction hr with
  | refl => exact hp
  | tail hxy hyz ih =>
      exact permissible_from_C0_stays hε hsmall ih hyz

lemma reachable_from_C1_stays {ε p q : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 72)
    (hp : p ∈ C1 ε) (hr : Reachable (E ε) (T ε) p q) :
    q ∈ C1 ε := by
  induction hr with
  | refl => exact hp
  | tail hxy hyz ih =>
      exact permissible_from_C1_stays hε hsmall ih hyz

lemma C0_diameter {ε x y : ℝ} (hε : 0 < ε) (hx : x ∈ C0 ε) (hy : y ∈ C0 ε) :
    |x - y| ≤ 12 * ε := by
  have hx0 := C0_nonneg hε hx
  have hy0 := C0_nonneg hε hy
  have hxU := C0_upper hε hx
  have hyU := C0_upper hε hy
  rw [abs_le]
  constructor <;> linarith

lemma C1_diameter {ε x y : ℝ} (hε : 0 < ε) (hx : x ∈ C1 ε) (hy : y ∈ C1 ε) :
    |x - y| ≤ 12 * ε := by
  have hx0 := reflect_C1_mem_C0 hx
  have hy0 := reflect_C1_mem_C0 hy
  have h := C0_diameter hε hx0 hy0
  have heq : (1 - x) - (1 - y) = -(x - y) := by ring
  rw [heq, abs_neg] at h
  exact h

/-- Main counterexample theorem: every reachable point remains at distance < 1/3
from its starting point, no matter how many permissible steps are taken. -/
theorem two_cluster_counterexample
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 72) :
    (0 ∈ E ε) ∧ (1 ∈ E ε) ∧
    (∀ x ∈ E ε, x ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ p ∈ E ε, T ε p ∈ E ε ∧ ε < |p - T ε p|) ∧
    (∀ p ∈ E ε, ∀ q, Reachable (E ε) (T ε) p q → |q - p| < 1 / 3) := by
  refine ⟨zero_mem_E ε, one_mem_E ε, E_subset_unit_interval hε hsmall, ?_, ?_⟩
  · intro p hp
    exact ⟨T_maps_E hε hsmall hp, displacement_T hε hsmall hp⟩
  · intro p hp q hr
    rw [E] at hp
    rcases Finset.mem_union.mp hp with hp0 | hp1
    · have hq0 := reachable_from_C0_stays hε hsmall hp0 hr
      have hd := C0_diameter hε hq0 hp0
      linarith
    · have hq1 := reachable_from_C1_stays hε hsmall hp1 hr
      have hd := C1_diameter hε hq1 hp1
      linarith

/-- There are counterexamples with epsilon arbitrarily small. -/
theorem arbitrarily_small_counterexamples :
    ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ε < η ∧ ε < 1 / 72 ∧
      (∀ p ∈ E ε, ∀ q, Reachable (E ε) (T ε) p q → |q - p| < 1 / 3) := by
  intro η hη
  let ε := min (η / 2) (1 / 144 : ℝ)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hεη : ε < η := by
    dsimp [ε]
    have hle : min (η / 2) (1 / 144 : ℝ) ≤ η / 2 := min_le_left _ _
    linarith
  have hsmall : ε < 1 / 72 := by
    dsimp [ε]
    have hle : min (η / 2) (1 / 144 : ℝ) ≤ (1 / 144 : ℝ) := min_le_right _ _
    norm_num at hle ⊢
  refine ⟨ε, hε, hεη, hsmall, ?_⟩
  exact (two_cluster_counterexample hε hsmall).2.2.2.2

/-- The explicit two-cluster construction satisfies every hypothesis in the
printed problem. -/
lemma constructed_admissible {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 72) :
    Admissible ε (E ε) (T ε) := by
  refine ⟨hε, zero_mem_E ε, one_mem_E ε, E_subset_unit_interval hε hsmall, ?_⟩
  intro p hp
  exact ⟨T_maps_E hε hsmall hp, displacement_T hε hsmall hp⟩

/-- Strong failure of the printed conclusion: for the two-cluster example,
`EscapesWithin N` fails for every finite step budget `N`. -/
theorem not_escapesWithin_any {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 72)
    (N : ℕ) : ¬ EscapesWithin N (E ε) (T ε) := by
  intro hescape
  rcases hescape 0 (zero_mem_E ε) with ⟨n, hn, q, hqE, hreachN, hfar⟩
  have hreach : Reachable (E ε) (T ε) 0 q := hreachN.toReachable
  have hnear : |q - 0| < (1 / 3 : ℝ) :=
    (two_cluster_counterexample hε hsmall).2.2.2.2 0 (zero_mem_E ε) q hreach
  linarith

/-- Exact formal negation of the universal-`k` assertion in the literal
printed Ulam Problem 164. -/
theorem no_universal_k : ¬ ∃ k : ℝ, UniversalBound k := by
  rintro ⟨k, hk⟩
  let ε : ℝ := 1 / 144
  have hε : 0 < ε := by
    dsimp [ε]
    norm_num
  have hsmall : ε < 1 / 72 := by
    dsimp [ε]
    norm_num
  have hadm : Admissible ε (E ε) (T ε) := constructed_admissible hε hsmall
  have hescape : EscapesWithin ⌊k / ε⌋₊ (E ε) (T ε) :=
    hk.2 ε (E ε) (T ε) hadm
  exact not_escapesWithin_any hε hsmall ⌊k / ε⌋₊ hescape

end

end Ulam164
