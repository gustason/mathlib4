/-
Copyright (c) 2026 Gustas Mickus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gustas Mickus
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Bonferroni inequalities

This file proves the Bonferroni inequalities for a finite family of sets. These inequalities bound
the indicator of the union by truncating the alternating inclusion-exclusion sum.

## Main results

* `Finset.indicator_biUnion_le_sum_powerset_of_odd`
* `Finset.sum_powerset_le_indicator_biUnion_of_even`

The bounds hold for any nonnegative function. The usual cardinality version is obtained by taking
the function to be constantly $1$.
-/

public section

namespace Finset
variable {ι α G : Type*}

/-- The alternating sum of the numbers of subsets of `u` of size at most $m$. -/
lemma sum_powerset_filter_card_le_neg_one_pow (u : Finset ι) (m : ℕ) :
    ∑ t ∈ u.powerset with #t ≤ m, (-1 : ℤ) ^ #t =
      ∑ k ∈ range (m + 1), (-1 : ℤ) ^ k * (#u).choose k := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := card) (t := range (m + 1))
    (fun t ht ↦ mem_range.2 (Nat.lt_succ_of_le (mem_filter.1 ht).2))]
  refine sum_congr rfl fun k hk ↦ ?_
  have : (u.powerset.filter (#· ≤ m)).filter (#· = k) = u.powersetCard k := by
    rw [powersetCard_eq_filter, filter_filter]
    refine filter_congr fun t _ ↦ ⟨And.right, ?_⟩
    rintro rfl
    exact ⟨Nat.lt_succ_iff.1 (mem_range.1 hk), rfl⟩
  rw [this, sum_congr rfl fun t ht ↦ by rw [(mem_powersetCard.1 ht).2], sum_const,
    card_powersetCard, nsmul_eq_mul, mul_comm]

/-- The truncated inclusion-exclusion coefficient sum over nonempty subsets, in closed form. -/
lemma sum_powerset_filter_nonempty_card_le (u : Finset ι) (hu : u.Nonempty) (m : ℕ) :
    ∑ t ∈ u.powerset with t.Nonempty ∧ #t ≤ m, (-1 : ℤ) ^ (#t + 1) =
      1 - (-1) ^ m * (#u - 1).choose m := by
  classical
  have key (t : Finset ι) :
      (if t.Nonempty ∧ #t ≤ m then (-1 : ℤ) ^ (#t + 1) else 0) =
        (if t = ∅ then 1 else 0) - (if #t ≤ m then (-1 : ℤ) ^ #t else 0) := by
    obtain rfl | ht := t.eq_empty_or_nonempty
    · simp
    · simp only [ht, true_and, ht.ne_empty, ite_false, zero_sub, pow_succ, mul_neg_one]
      split_ifs <;> simp
  rw [sum_filter, sum_congr rfl fun t _ ↦ key t, sum_sub_distrib, sum_ite_eq']
  simp only [empty_mem_powerset, ite_true]
  rw [← sum_filter, sum_powerset_filter_card_le_neg_one_pow]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hu.card_ne_zero
  rw [hn, Int.alternating_sum_range_choose_eq_choose, Nat.succ_sub_one]

variable [AddCommGroup G]

/-- Only subsets `t` all of whose sets contain `a` contribute to a sum of intersection
indicators. -/
lemma sum_powerset_filter_zsmul_indicator_iInter (s : Finset ι) (S : ι → Set α) (f : α → G)
    (a : α) (p : Finset ι → Prop) [DecidablePred p] (c : Finset ι → ℤ)
    [DecidablePred (a ∈ S ·)] :
    ∑ t ∈ s.powerset with p t, c t • Set.indicator (⋂ i ∈ t, S i) f a =
      (∑ t ∈ (s.filter (a ∈ S ·)).powerset with p t, c t) • f a := by
  classical
  rw [sum_smul]
  symm
  refine sum_subset_zero_on_sdiff ?_ ?_ ?_
  · exact filter_subset_filter _ (powerset_mono.2 (filter_subset _ _))
  · intro t ht
    simp only [mem_sdiff, mem_filter, mem_powerset] at ht
    obtain ⟨⟨hts, hpt⟩, hn⟩ := ht
    have : ¬ ∀ i ∈ t, a ∈ S i :=
      fun h ↦ hn ⟨fun i hi ↦ mem_filter.2 ⟨hts hi, h i hi⟩, hpt⟩
    rw [Set.indicator_of_notMem (by simpa only [Set.mem_iInter] using this), smul_zero]
  · intro t ht
    simp only [mem_filter, mem_powerset] at ht
    rw [Set.indicator_of_mem (Set.mem_iInter₂.2 fun i hi ↦ (mem_filter.1 (ht.1 hi)).2)]

variable [PartialOrder G] [IsOrderedAddMonoid G]

/-- **Bonferroni inequality**: truncating the inclusion-exclusion sum at an odd number of terms
gives an upper bound for the indicator of a finite union. -/
theorem indicator_biUnion_le_sum_powerset_of_odd (s : Finset ι) (S : ι → Set α) {f : α → G}
    {a : α} (hf : 0 ≤ f a) {m : ℕ} (hm : Odd m) :
    Set.indicator (⋃ i ∈ s, S i) f a ≤ ∑ t ∈ s.powerset with t.Nonempty ∧ #t ≤ m,
      (-1) ^ (#t + 1) • Set.indicator (⋂ i ∈ t, S i) f a := by
  classical
  rw [sum_powerset_filter_zsmul_indicator_iInter]
  obtain hu | hu := (s.filter (a ∈ S ·)).eq_empty_or_nonempty
  · rw [Set.indicator_of_notMem (by simpa [filter_eq_empty_iff] using hu), hu]
    simp [filter_singleton]
  · obtain ⟨i, hi⟩ := hu
    rw [Set.indicator_of_mem
      (Set.mem_iUnion₂.2 ⟨i, (mem_filter.1 hi).1, (mem_filter.1 hi).2⟩),
      sum_powerset_filter_nonempty_card_le _ ⟨i, hi⟩, hm.neg_one_pow]
    conv_lhs => rw [← one_zsmul (f a)]
    exact zsmul_le_zsmul_left hf (by simp)

/-- **Bonferroni inequality**: truncating the inclusion-exclusion sum at an even number of terms
gives a lower bound for the indicator of a finite union. -/
theorem sum_powerset_le_indicator_biUnion_of_even (s : Finset ι) (S : ι → Set α) {f : α → G}
    {a : α} (hf : 0 ≤ f a) {m : ℕ} (hm : Even m) :
    ∑ t ∈ s.powerset with t.Nonempty ∧ #t ≤ m,
      (-1) ^ (#t + 1) • Set.indicator (⋂ i ∈ t, S i) f a ≤
        Set.indicator (⋃ i ∈ s, S i) f a := by
  classical
  rw [sum_powerset_filter_zsmul_indicator_iInter]
  obtain hu | hu := (s.filter (a ∈ S ·)).eq_empty_or_nonempty
  · rw [Set.indicator_of_notMem (by simpa [filter_eq_empty_iff] using hu), hu]
    simp [filter_singleton]
  · obtain ⟨i, hi⟩ := hu
    rw [Set.indicator_of_mem
      (Set.mem_iUnion₂.2 ⟨i, (mem_filter.1 hi).1, (mem_filter.1 hi).2⟩),
      sum_powerset_filter_nonempty_card_le _ ⟨i, hi⟩, hm.neg_one_pow]
    conv_rhs => rw [← one_zsmul (f a)]
    exact zsmul_le_zsmul_left hf (by simp)

end Finset
