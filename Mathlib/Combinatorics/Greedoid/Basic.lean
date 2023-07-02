-- Possible requirements: import Mathlib.Computability.Language
import Mathlib.Data.List.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Data.List.Infix
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.List
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Tactic.TFAE
import Mathlib.Tactic.WLOG

protected theorem List.exists_maximal_suffix {α : Type _} {l : List α} {p : List α → Prop}
  (hp_empty : p []) (hp_suffix : ∀ l, p l → (∀ l', l' <:+ l → p l')) :
    ∃ l', l' <:+ l ∧ p l' ∧ (∀ l'', l'' <:+ l → p l'' → l''.length ≤ l'.length) := by
  induction' l with h l ih <;> simp [hp_empty]
  have ⟨l', hl'₁, hl'₂, hl'₃⟩ := ih
  by_cases h₁ : l' = l
  . by_cases h₂ : p (h :: l)
    . exists h :: l
      simp only [List.suffix_rfl, h₂, true_and]
      exact fun _ h _ => List.isSuffix.length_le h
    . exists l
      rw [h₁] at hl'₂
      simp only [suffix_cons, hl'₂, true_and]
      intro _ h₃ h₄
      rw [List.suffix_cons_iff] at h₃
      apply h₃.elim <;> intro h₃
      . rw [h₃] at h₄
        contradiction
      . exact List.isSuffix.length_le h₃
  . exists l'
    simp only [hl'₂, true_and]
    constructor
    . rw [List.suffix_cons_iff]; exact Or.inr hl'₁
    . intro _ h₂ h₃
      rw [List.suffix_cons_iff] at h₂
      apply h₂.elim <;> intro h₂
      . exfalso
        exact h₁ (List.isSuffix.eq_of_length hl'₁ (Nat.le_antisymm (List.isSuffix.length_le hl'₁)
          (hl'₃ _ List.suffix_rfl (hp_suffix _ (h₂ ▸ h₃) _ (List.suffix_cons _ _)))))
      . exact hl'₃ _ h₂ h₃

/-  Note: We distinguish `w` as a `Word` from `l` as a `List`, but use the same type
    as there are so many functionalities given with `List`. -/

/-- The exchange axiom for set systems -/
def exchangeAxiom {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) :=
  {s₁ : Finset α} → (hs₁ : s₁ ∈ Sys) →
  {s₂ : Finset α} → (hs₂ : s₂ ∈ Sys) →
  (hs : s₁.card > s₂.card) →
    ∃ x ∈ s₁ \ s₂, s₂ ∪ {x} ∈ Sys

instance {α : Type _} [DecidableEq α] :
    DecidablePred (@exchangeAxiom α _) := fun Sys =>
  if h : ∀ {s₁}, s₁ ∈ Sys → ∀ {s₂}, s₂ ∈ Sys → s₁.card > s₂.card →
    ∃ x, x ∈ s₁ \ s₂ ∧ s₂ ∪ {x} ∈ Sys
  then isTrue (by intro s₁ hs₁ s₂ hs₂ hs; simp at h; simp; exact h hs₁ hs₂ hs)
  else isFalse (by intro h'; apply h; clear h; simp [exchangeAxiom] at h'; simp; apply h')

namespace Language

/-- Simple language is a language that every word does not have duplicates.
    Due to this property, we may define such a language as `Finset (List α)`,
    as it is easier to handle.  -/
class Simple {α : Type _} [DecidableEq α] (Lang : Finset (List α)) where
  simple : ∀ w ∈ Lang, w.Nodup

theorem simple_language_word_head_notin_tail {α : Type _} [DecidableEq α] (Lang : Finset (List α))
    [Simple Lang] {h : α} {t : List α} (ht : h :: t ∈ Lang) : h ∉ t := by
  have := ‹Simple Lang›.simple (h :: t) ht
  simp at this
  exact this.1

/-- Normal language contains no loops; every alphabet is in some word in the language. -/
class Normal {α : Type _} [DecidableEq α] (Lang : Finset (List α))
    extends Simple Lang where
  no_loops : ∀ a : α, ∃ w ∈ Lang, a ∈ w

/-- Hereditary language contains the emptyset and the prefix of every word in the language. -/
class Hereditary {α : Type _} [DecidableEq α] (Lang : Finset (List α))
    extends Simple Lang where
  contains_empty : [] ∈ Lang
  contains_prefix : ∀ w₁ w₂, w₂ ++ w₁ ∈ Lang → w₁ ∈ Lang

def toAssociatedSetSystem {α : Type _} [DecidableEq α] (Lang : Finset (List α)) :=
    Lang.image (fun w : List α ↦ w.toFinset)

end Language

namespace SetSystem

/-- Accessible set systems are defined as an associated set system of hereditary language;
    here we only pick its properties. -/
class Accessible {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) where
  contains_empty : ∅ ∈ Sys
  accessible : ∀ s ∈ Sys, s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ Sys

instance toAssociatedSetSystem_Accessible {α : Type _} [DecidableEq α] (Lang : Finset (List α))
  [Language.Hereditary Lang] :
    Accessible (Language.toAssociatedSetSystem Lang) where
  contains_empty := by
    simp [Language.toAssociatedSetSystem, ‹Language.Hereditary Lang›.contains_empty]
  accessible := by
    simp [Language.toAssociatedSetSystem]
    intro w hw₁ hw₂
    match w with
    | h :: w =>
      exists h
      simp
      exists w
      apply And.intro (‹Language.Hereditary Lang›.contains_prefix w [h] hw₁)
      rw [Finset.insert_sdiff_of_mem _ (by simp)]
      have := Language.simple_language_word_head_notin_tail _ hw₁
      simp [this]

def toHereditaryLanguage {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) [Accessible Sys] :=
  let perm_set := Finset.biUnion (Sys.map ⟨fun s => s.val.lists, by
    intro s
    have : ∃ l, l ∈ s.val.lists := by
      induction' s using Finset.induction_on with a s hs ih
      . exists []; simp
      . let ⟨l, hl⟩ := ih
        exists a :: l
        have : a ∉ l := by
          intro h'; apply hs; clear hs
          simp [Multiset.mem_lists_iff] at hl
          rw [Finset.mem_def, hl]
          simp [h']
        simp_all
    intro t h
    simp at h
    let ⟨l, hl⟩ := this
    have hr := h ▸ hl
    have hl := (s.val.mem_lists_iff l).mp hl
    have hr := (t.val.mem_lists_iff l).mp hr
    apply Finset.eq_of_veq
    simp only [hl, hr]⟩) id
  perm_set.filter (fun l => ∀ l' ∈ l.tails, l'.toFinset ∈ Sys)

instance toHereditaryLanguage_Hereditary {α : Type _} [DecidableEq α] (Sys : Finset (Finset α))
  [Accessible Sys] :
    Language.Hereditary (toHereditaryLanguage Sys) where
  simple _ hw := by
    simp [toHereditaryLanguage] at hw
    let ⟨⟨a, _⟩, _⟩ := hw
    have : a.val.Nodup := a.nodup
    simp_all
  contains_empty := by simp [toHereditaryLanguage, ‹Accessible Sys›.contains_empty]
  contains_prefix w₁ w₂ hw := by
    simp [toHereditaryLanguage] at *
    let ⟨⟨a, _, ha⟩, h⟩ := hw; clear hw
    have : (Multiset.ofList _).Nodup := ha ▸ a.nodup
    simp only [Multiset.coe_nodup] at this
    constructor
    . exists w₁.toFinset
      apply And.intro (h _ (Or.inl ⟨[], by simp; exists w₂; simp only [List.append_nil]⟩)) _
      simp
      rw [List.dedup_eq_self.mpr]
      exact List.Nodup.of_append_right this
    . intro w hw
      apply h _
      by_cases (w = w₁)
      . exact Or.inl ⟨[], by simp [h, List.nil_suffix]⟩
      . apply Or.inr
        cases w₁
        . simp_all
        . rw [List.suffix_cons_iff] at hw
          simp; apply hw.elim <;> tauto

theorem accessible_system_smaller_feasible_set_helper {α : Type _} [DecidableEq α]
  {Sys : Finset (Finset α)} [Accessible Sys]
  {s : Finset α} (hs₁ : s ≠ ∅) (hs₂ : s ∈ Sys) {n : ℕ} (hn : n ≤ s.card) :
    ∃ s' ∈ Sys, s' ⊆ s ∧ s'.card + n = s.card := by
  induction' n with n ih generalizing s
  . exists s
  . have ⟨s', hs'₁, hs'₂, hs'₃⟩ := ih hs₁ hs₂ (Nat.le_trans (by simp_arith) hn)
    let ⟨a, ha₁, ha₂⟩ := ‹Accessible Sys›.accessible _ hs'₁ (by
      intro h'
      simp [h'] at hs'₃
      rw [← hs'₃] at hn
      simp_arith at hn)
    exists s' \ {a}
    simp [ha₂, Finset.card_sdiff (fun x hx => by simp at hx; simp [hx, ha₁] : {a} ⊆ s')]
    apply And.intro (Finset.Subset.trans (Finset.sdiff_subset s' {a}) hs'₂)
    rw [Nat.succ_eq_add_one, ← Nat.sub_add_comm, ← Nat.add_assoc, Nat.add_sub_cancel, hs'₃]
    have h₁ : s'.card = s.card - n := (Nat.sub_eq_of_eq_add hs'₃.symm).symm
    have h₂ : 1 ≤ s.card - n := Nat.le_sub_of_add_le (Nat.succ_eq_one_add n ▸ hn)
    simp only [h₁, h₂]

theorem accessible_system_smaller_feasible_set {α : Type _} [DecidableEq α]
  {Sys : Finset (Finset α)} [Accessible Sys]
  {s : Finset α} (hs₁ : s ≠ ∅) (hs₂ : s ∈ Sys) {n : ℕ} (hn : n ≤ s.card) :
    ∃ s' ∈ Sys, s' ⊆ s ∧ s'.card = n := by
  have ⟨s', hs'₁, hs'₂, hs'₃⟩ := accessible_system_smaller_feasible_set_helper hs₁ hs₂
    (Nat.sub_le _ _ : s.card - n ≤ s.card)
  exists s'
  simp_arith [hs'₁, hs'₂]
  have : n ≤ Finset.card s + Finset.card s' := Nat.le_trans hn (by simp)
  rw [← Nat.add_sub_assoc hn, Nat.add_comm, Nat.sub_eq_iff_eq_add this] at hs'₃
  simp_arith at hs'₃
  exact hs'₃

protected theorem induction_on_accessible {α : Type _} [Fintype α] [DecidableEq α]
  {p : Finset α → Prop}
  {Sys : Finset (Finset α)} [Accessible Sys]
  (s : Finset α) (hs : s ∈ Sys)
  (empty : p ∅)
  (insert : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → s ∈ Sys → s ∪ {a} ∈ Sys → p s → p (s ∪ {a})) :
    p s := by
  by_cases s = ∅ <;> simp only [h, empty]
  have ⟨x, hx₁, hx₂⟩ := ‹Accessible Sys›.accessible _ hs h
  have := SetSystem.induction_on_accessible _ hx₂ empty insert
  have := insert (by simp) hx₂ (by
    simp only [hx₁, Finset.sdiff_union_self_eq_union]
    rw [Finset.union_comm, ← Finset.insert_eq]
    simp only [hx₁, Finset.insert_eq_of_mem, hs] : s \ {x} ∪ {x} ∈ Sys) this
  rw [Finset.sdiff_union_self_eq_union, Finset.union_comm, ← Finset.insert_eq,
    Finset.insert_eq_of_mem hx₁] at this
  exact this
termination_by induction_on_accessible => s.card
decreasing_by
  simp_wf
  rw [Finset.card_sdiff (fun x' hx' => (Finset.eq_of_mem_singleton hx') ▸ hx₁)]
  exact Nat.sub_lt (Nat.zero_lt_of_ne_zero (Finset.card_ne_zero_of_mem hx₁))
    (by simp only [Finset.card_singleton])

theorem mem_toHereditaryLanguage {α : Type _} [Fintype α] [DecidableEq α]
  {Sys : Finset (Finset α)} [Accessible Sys]
  {s : Finset α} (hs : s ∈ Sys) :
    ∃ w ∈ toHereditaryLanguage Sys, w.toFinset = s := by
  have := toHereditaryLanguage_Hereditary Sys
  apply SetSystem.induction_on_accessible s hs
  . exists ∅
    simp only [List.empty_eq, List.toFinset_nil, and_true, this.contains_empty]
  . rintro a s ha _ hs ⟨w, hw₁, hw₂⟩
    exists a :: w
    rw [Finset.union_comm, ← Finset.insert_eq]
    simp only [List.toFinset_cons, hw₂, and_true]
    simp [toHereditaryLanguage, hw₂]
    have a_notin_w : a ∉ w := by simp only [← hw₂, List.mem_toFinset] at ha; simp only [ha]
    constructor <;> try apply And.intro
    . exists (s ∪ {a})
      simp only [hs, true_and]
      rw [← hw₂, Finset.union_comm, ← Finset.insert_eq]
      simp [this.simple _ hw₁, List.Nodup.dedup, a_notin_w]
    . rw [Finset.union_comm, ← Finset.insert_eq] at hs
      exact hs
    . rintro w' ⟨w'', hw''⟩
      have := this.contains_prefix w' w'' (hw'' ▸ hw₁)
      simp [toHereditaryLanguage] at this
      exact this.2 _ ⟨[], List.nil_append _⟩

end SetSystem

theorem hereditary_language_lemma_helper {α : Type _} [DecidableEq α] {w₁ w₂ : List α}
  (hw₁ : w₂ <:+ w₁) (hw₂ : w₂.length < w₁.length) :
    ∃ x, x :: w₂ <:+ w₁ := by
  cases' w₁ with h w₁ <;> try contradiction
  have ⟨w, hw⟩ := hw₁
  cases' w₂ with h' w₂
  . cases' w₁ with h' w₁
    . exists h; exact List.suffix_rfl
    . simp at hw
      have ⟨x, w', hw'⟩ := hereditary_language_lemma_helper
        (⟨h' :: w₁, by simp⟩ : [] <:+ h' :: w₁) (by simp)
      exists x; exists h :: w'; simp only [List.cons_append, hw']
  . simp at hw₂
    have hw₂ := Nat.lt_of_succ_lt_succ hw₂
    simp_arith at hw₂
    rw [Nat.le_iff_lt_or_eq] at hw₂
    have : w₂.length + 1 = (h' :: w₂).length := rfl
    apply hw₂.elim <;> intro hw₂
    . rw [this] at hw₂
      have ⟨x, w', hw'⟩ := hereditary_language_lemma_helper ⟨w.tail, by
        cases' w with h'' w
        . simp at hw; simp_arith [hw.2] at hw₂
        . simp at hw; simp [hw.2]⟩ hw₂
      exists x; exists h :: w'; simp only [List.cons_append, hw']
    . exists h
      have : h' :: w₂ = w₁ := by
        rw [this] at hw₂
        have : h' :: w₂ <:+ w₁ := by
          exists w.tail
          cases' w with h'' w
          . simp at hw; simp [hw.2] at hw₂
          . simp at hw; simp [hw.2]
        exact List.eq_of_suffix_of_length_eq this hw₂
      simp only [this, List.suffix_rfl]
termination_by hereditary_language_lemma_helper w₁ w₂ _ _ => w₁.length + w₂.length

theorem hereditary_language_lemma {α : Type _} [DecidableEq α] {Lang : Finset (List α)}
  [Language.Hereditary Lang] :
    Lang = SetSystem.toHereditaryLanguage (Language.toAssociatedSetSystem Lang) ↔
      (∀ w₁ ∈ Lang, ∀ w₂ ∈ Lang, ∀ x ∈ (w₁.toFinset \ w₂.toFinset),
        w₁.toFinset = w₂.toFinset ∪ {x} → x :: w₂ ∈ Lang) := by
  constructor <;> intro h
  . intro w₁ hw₁ w₂ hw₂ x hx₁ hx₂
    rw [h]
    have hacc := SetSystem.toAssociatedSetSystem_Accessible Lang
    have hher := SetSystem.toHereditaryLanguage_Hereditary (Language.toAssociatedSetSystem Lang)
    simp [SetSystem.toHereditaryLanguage]
    have w₁_nodup := ‹Language.Hereditary Lang›.simple _ hw₁
    have w₂_nodup := ‹Language.Hereditary Lang›.simple _ hw₂
    constructor <;> try apply And.intro
    . exists w₁.toFinset
      simp at hx₁
      simp [w₁_nodup, List.Nodup.dedup]
      constructor
      . simp [Language.toAssociatedSetSystem]; exists w₁
      . apply List.perm_of_nodup_nodup_toFinset_eq w₁_nodup _
          (by simp [hx₂, Finset.insert_eq, Finset.union_comm])
        simp only [List.nodup_cons, hx₁, not_false_eq_true, w₂_nodup, and_self]
    . simp [Language.toAssociatedSetSystem]
      exists w₁
      simp only [hw₁, hx₂, List.mem_toFinset, Finset.insert_eq, Finset.union_comm, and_self]
    . rintro w ⟨w', hw'⟩
      have := hher.3 w w' (hw' ▸ h ▸ hw₂)
      simp [SetSystem.toHereditaryLanguage] at this
      exact this.2 _ ⟨[], List.nil_append _⟩
  . ext w
    constructor <;> intro h₀
    . simp [SetSystem.toHereditaryLanguage]
      constructor
      . exists w.toFinset
        apply And.intro (by simp [Language.toAssociatedSetSystem]; exists w)
        simp; rw [List.Nodup.dedup (‹Language.Hereditary Lang›.1.1 _ h₀)]
      . rintro w' ⟨w'', hw''⟩
        simp [Language.toAssociatedSetSystem]
        exists w'
        simp; exact ‹Language.Hereditary Lang›.3 w' w'' (hw'' ▸ h₀)
    . simp [SetSystem.toHereditaryLanguage, Language.toAssociatedSetSystem] at h₀
      let ⟨⟨w₁, hw₁₁, hw₁₂⟩, h₁⟩ := h₀
      have w₁_nodup := ‹Language.Hereditary Lang›.simple _ hw₁₁
      simp [w₁_nodup, List.Nodup.dedup] at hw₁₂
      have w_nodup := (List.Perm.nodup_iff hw₁₂).mpr w₁_nodup
      have ⟨w₀, hw₀⟩ : ∃ w₀ ∈ Lang, w₀ <:+ w ∧ (∀ w' ∈ Lang, w' <:+ w → w'.length ≤ w₀.length) := by
        have ⟨w₀, hw₀⟩ := @List.exists_maximal_suffix _ w (fun w' => w' ∈ Lang)
            ‹Language.Hereditary Lang›.contains_empty (by
              simp only
              rintro l₁ hl₁ l₂ ⟨l₃, hl₂⟩
              exact ‹Language.Hereditary Lang›.contains_prefix l₂ l₃ (hl₂ ▸ hl₁))
        exists w₀; tauto
      by_cases h₂ : w₀ = w
      . exact h₂ ▸ hw₀.1
      . have w₀_length := lt_iff_le_and_ne.mpr
          ⟨List.isSuffix.length_le hw₀.2.1, by
            contrapose h₂; simp at *; exact List.eq_of_suffix_of_length_eq hw₀.2.1 h₂⟩
        have ⟨x, hx⟩ : ∃ x, x :: w₀ <:+ w := hereditary_language_lemma_helper hw₀.2.1 w₀_length
        have : x ∉ w₀ := by
          have ⟨w', hw'⟩ := hx
          have := (List.nodup_append.mp (hw' ▸ w_nodup : (w' ++ x :: w₀).Nodup)).2.1
          simp only [List.nodup_cons] at this
          simp only [this]
        have ⟨w₀', hw₀'⟩ : ∃ w₀' ∈ Lang, w₀'.toFinset = w₀.toFinset ∪ {x} := by
          have ⟨w', hw'⟩ := h₁ _ hx
          exists w'; simp at hw'; simp [hw', Finset.insert_eq, Finset.union_comm]
        have := hw₀.2.2 _ (h _ hw₀'.1 _ hw₀.1 x
          (by simp only [Finset.mem_sdiff, hw₀'.2]; simp [this]) hw₀'.2) hx
        simp_arith at this

namespace SetSystem

protected theorem Finset.card_induction_on {α : Type _} {p : Finset α → Prop} [DecidableEq α]
  (s : Finset α) (empty : p ∅)
    (insert : ∀ {s : Finset α},
      (∃ t : Finset α, t.card + 1 = s.card ∧ t ⊆ s ∧ p t) → p s) : p s := by
  induction' s using Finset.induction_on with a s ha ih
  . exact empty
  . exact insert ⟨s, by simp [ha], fun x hx => by simp; exact Or.inr hx, ih⟩

variable {α : Type _} [Fintype α] [DecidableEq α]

/-- Base of a set system is the collection of feasible sets which is maximal. -/
def base (Sys : Finset (Finset α)) : Finset (Finset α) :=
  Sys.filter (fun s => ∀ a, a ∉ s → s ∪ {a} ∉ Sys)

/-- Bases of a set `a` given a set system is
    the collection of feasible sets which is maximal in `a`. -/
def bases (Sys : Finset (Finset α)) (s : Finset α) : Finset (Finset α) :=
  Sys.filter (fun s' => s' ⊆ s ∧ (∀ a, a ∉ s' → a ∉ s ∨ s' ∪ {a} ∉ Sys))

theorem base_bases_eq {Sys : Finset (Finset α)} :
    base Sys = bases Sys Finset.univ := by ext s; simp [bases, base]

theorem basis_mem_feasible_set {Sys : Finset (Finset α)} {s b : Finset α} (hb : b ∈ bases Sys s) :
    b ∈ Sys := by
  simp only [bases, Finset.mem_filter] at hb
  exact hb.1

theorem basis_subseteq {Sys : Finset (Finset α)} {s b : Finset α} (hb : b ∈ bases Sys s) :
    b ⊆ s := by
  simp only [bases, Finset.mem_filter] at hb
  exact hb.2.1

theorem basis_maximal {Sys : Finset (Finset α)} {s b : Finset α} (hb : b ∈ bases Sys s)
  {a : α} (ha : a ∉ b) :
    a ∉ s ∨ b ∪ {a} ∉ Sys := by
  simp only [bases, Finset.mem_filter] at hb
  exact hb.2.2 a ha

theorem exists_bases_containing_feasible_set {Sys : Finset (Finset α)} {s a : Finset α}
  (hs₁ : s ∈ Sys) (hs₂ : s ⊆ a) :
    ∃ b ∈ bases Sys a, s ⊆ b := by
  by_cases (∀ x, x ∉ s → x ∉ a ∨ s ∪ {x} ∉ Sys)
  . exists s
    simp [bases, hs₁, hs₂]
    intro x hx; simp only [h, hx]
  . simp only [not_forall, exists_prop] at h
    let ⟨x, _, hx₂⟩ := h
    simp only [not_not, not_or] at hx₂
    let ⟨hx₂, hx₃⟩ := hx₂
    have ⟨b, hb⟩ := exists_bases_containing_feasible_set hx₃ (fun y hy => by
      simp at hy
      exact hy.elim (fun h => hs₂ h) (fun h => h ▸ hx₂) : s ∪ {x} ⊆ a)
    exists b
    simp only [hb.1, true_and]
    exact Finset.Subset.trans (Finset.subset_union_left _ _) hb.2
termination_by exists_bases_containing_feasible_set Sys s a _ _ => a.card - s.card
decreasing_by
  simp_wf
  have hx₁ := ‹x ∉ s›
  simp [hx₁]
  exact Nat.sub_lt_sub_left
    (Finset.card_lt_card ((Finset.ssubset_iff_of_subset hs₂).mpr ⟨x, hx₂, hx₁⟩))
    (by simp_arith)

theorem accessible_bases_nonempty {Sys : Finset (Finset α)} [Accessible Sys] {s : Finset α} :
    ∃ b, b ∈ bases Sys s :=
  let ⟨b, hb⟩ := exists_bases_containing_feasible_set
    ‹Accessible Sys›.contains_empty
    (Finset.empty_subset s)
  ⟨b, hb.1⟩

theorem accessible_self_mem_bases_of_inter {Sys : Finset (Finset α)} [Accessible Sys]
  {s₁ s₂ : Finset α} (hs : s₁ ∈ bases Sys (s₁ ∩ s₂)) :
    s₁ ⊆ s₂ := by
  intro x hx
  simp [bases] at hs
  have := hs.2.1 hx
  rw [Finset.mem_inter] at this
  tauto

end SetSystem

theorem card_lt_mem_sdiff {α : Type _} [DecidableEq α] {s₁ s₂ : Finset α} (hs : s₁.card < s₂.card) :
    ∃ x, x ∈ s₂ \ s₁ := by
  by_cases h : s₁ ⊆ s₂
  . by_contra' h'
    simp [← Finset.subset_iff] at h'
    simp only [Finset.Subset.antisymm_iff.mpr ⟨h, h'⟩, lt_self_iff_false] at hs
  . have ⟨x, hx⟩ := @card_lt_mem_sdiff _ _ (s₁ ∩ s₂) s₂
      (Nat.lt_of_le_of_lt (Finset.card_le_of_subset (Finset.inter_subset_left _ _)) hs)
    exists x; simp at hx; simp [hx]
termination_by card_lt_mem_sdiff s₁ _ _ => s₁.card
decreasing_by
  simp_wf
  apply (Nat.le_iff_lt_or_eq.mp (Finset.card_le_of_subset (Finset.inter_subset_left s₁ s₂))).elim
    (fun h => h)
  intro h₀
  exfalso; apply h
  rw [← Finset.inter_eq_left_iff_subset]
  apply Finset.eq_of_subset_of_card_le (Finset.inter_subset_left _ _)
  rw [h₀]

section ExchangeAxioms

open List Finset Language SetSystem

variable {α : Type _} [Fintype α] [DecidableEq α]

/-- A weak version of exchange axiom of set system version of greedoid -/
def weakExchangeAxiom (Sys : Finset (Finset α)) :=
  {s₁ : Finset α} → (hs₁ : s₁ ∈ Sys) →
  {s₂ : Finset α} → (hs₂ : s₂ ∈ Sys) →
  (hs : s₁.card = s₂.card + 1) →
    ∃ x ∈ s₁ \ s₂, s₂ ∪ {x} ∈ Sys

/-- A weaker version of exchange axiom of set system version of greedoid -/
def weakerExchangeAxiom (Sys : Finset (Finset α)) :=
  {s : Finset α} →
  {x : α} → (hx₁ : x ∉ s) → (hx₂ : s ∪ {x} ∈ Sys) →
  {y : α} → (hy₁ : y ∉ s) → (hy₂ : s ∪ {y} ∈ Sys) →
  {z : α} → (hz : z ∉ s) → (hxz₁ : x ≠ z) →
  (hxz₂ : s ∪ {x, z} ∈ Sys) → (hxy : s ∪ {x, y} ∉ Sys) →
    s ∪ {y, z} ∈ Sys

theorem exchangeAxiom_weakExchangeAxiom_iff {Sys : Finset (Finset α)} [Accessible Sys] :
    exchangeAxiom Sys ↔ weakExchangeAxiom Sys := by
  constructor <;> intro h
  . intro _ hs₁ _ hs₂ hs
    let ⟨x, hx⟩ := h hs₁ hs₂ (by simp [hs])
    exact ⟨x, hx⟩
  . intro s₁ hs₁ s₂ hs₂ hs
    have ⟨a, ha₁, ha₂, ha₃⟩ := accessible_system_smaller_feasible_set
      (fun h' => (Nat.not_eq_zero_of_lt hs) (card_eq_zero.mpr h')) hs₁
      (by simp_arith at hs; exact hs : s₂.card < s₁.card)
    have ⟨x, hx₁, hx₂⟩ := h ha₁ hs₂ ha₃
    exists x; simp_all; exact ha₂ hx₁.1

mutual
  theorem weakerExchangeAxiom_exchangeAxiom_helper {Sys : Finset (Finset α)} [Accessible Sys]
    (hSys : weakerExchangeAxiom Sys)
    {s₁ : Finset α} (hs₁ : s₁ ∈ Sys)
    {s₂ : Finset α} (hs₂ : s₂ ∈ Sys)
    (hs : s₁.card = s₂.card + 1) :
      ∃ x ∈ s₁ \ s₂, s₂ ∪ {x} ∈ Sys := by
    have ⟨c, hc₁⟩ := @accessible_bases_nonempty _ _ _ Sys _ (s₁ ∩ s₂)
    by_cases h₀ : c = s₂
    . have ⟨x, hx⟩ := card_lt_mem_sdiff (hs ▸ (Nat.lt_succ_self s₂.card) : s₂.card < s₁.card)
      exists x
      rw [mem_sdiff] at *
      simp only [hx, hx.1, true_and]
      rw [h₀, Finset.inter_comm] at hc₁
      have : (s₁ \ s₂).card = 1 := by
        rw [Finset.card_sdiff (accessible_self_mem_bases_of_inter hc₁), hs,
          Nat.succ_sub (Nat.le.refl), Nat.sub_self]
      have ⟨y, hy⟩ := Finset.card_eq_one.mp this
      have : x = y := by
        have ⟨z, _, hz⟩ := (Finset.singleton_iff_unique_mem _).mp ⟨y, hy⟩
        simp only [mem_sdiff, and_imp] at hz
        rw [hz _ hx.1 hx.2]
        have : y ∈ s₁ \ s₂ := hy ▸ Finset.mem_singleton_self y
        rw [mem_sdiff] at this
        exact (hz _ this.1 this.2).symm
      rw [this]
      have : s₁ = s₂ ∪ {y} := by
        rw [← hy]
        simp only [union_sdiff_self_eq_union, right_eq_union_iff_subset,
          accessible_self_mem_bases_of_inter hc₁]
      exact this ▸ hs₁
    . have : s₂.card > c.card :=
        have := (Finset.subset_inter_iff.mp (basis_subseteq hc₁)).2
        Finset.card_lt_card (ssubset_def.mpr ⟨this, fun h' => h₀ (Finset.Subset.antisymm this h')⟩)
      have ⟨a, ha₁, ha₂⟩ :=
        weakerExchangeAxiom_exchangeAxiom hSys hs₂ (basis_mem_feasible_set hc₁) this
      have : s₁.card > (c ∪ {a}).card :=
        hs ▸ Nat.lt_of_le_of_lt (Finset.card_union_le c {a}) (Nat.succ_lt_succ_iff.mpr this)
      have ⟨s₂', hs₂'⟩ : ∃ s₂' ∈ Sys, c ∪ {a} ⊆ s₂' ∧ s₂' ⊆ s₁ ∪ {a} ∧ s₂.card = s₂'.card := by
        sorry
      by_cases h₁ : (s₁ ∪ s₂').card < (s₁ ∪ s₂).card
      . sorry
      . have h₁ : (s₁ ∪ s₂').card = (s₁ ∪ s₂).card := by
          sorry
        sorry

  theorem weakerExchangeAxiom_exchangeAxiom {Sys : Finset (Finset α)} [Accessible Sys]
    (hSys : weakerExchangeAxiom Sys) :
      exchangeAxiom Sys := by
    intro s₁' hs₁' s₂ hs₂ hs
    have ⟨s₁, hs₁, hs₃, hs₄⟩ := accessible_system_smaller_feasible_set
      (fun h => (Nat.not_eq_zero_of_lt hs) (card_eq_zero.mpr h)) hs₁' hs
    have ⟨x, hx⟩ := weakerExchangeAxiom_exchangeAxiom_helper hSys hs₁ hs₂ hs₄
    exists x; simp_all; exact hs₃ hx.1.1

end

theorem exchange_axioms_TFAE {Sys : Finset (Finset α)} [Accessible Sys] :
    TFAE [exchangeAxiom Sys, weakExchangeAxiom Sys, weakerExchangeAxiom Sys] := by
  tfae_have 1 ↔ 2
  { exact exchangeAxiom_weakExchangeAxiom_iff }
  tfae_have 2 → 3
  {
    intro h s x hx₁ _ y hy₁ hy₂ z hz hxz₁ hxz₂ hxy
    let ⟨z', hz₁', hz₂'⟩ := h hxz₂ hy₂ (by
      simp [hxz₁, hx₁]
      rw [union_comm, union_comm s {y}, ← insert_eq, ← insert_eq]
      simp [hy₁, hz])
    simp at hz₁'
    let ⟨h₁, h₂⟩ := hz₁'
    apply h₁.elim <;> intro h₁ <;> try (apply h₁.elim <;> intro h₁)
    . simp [h₁] at hz₂'
      exfalso
      apply hxy
      have : s ∪ {x, y} = s ∪ ({y} ∪ {x}) := by
        simp
        rw [union_comm _ ({y} ∪ {x}), union_comm {y} {x}, union_assoc, union_comm {y} s]
        rfl
      rw [this]
      exact hz₂'
    . exfalso
      exact h₂ (Or.inl h₁)
    . simp [h₁] at h₂ hz₂'
      have : s ∪ {y, z} = s ∪ ({y} ∪ {z}) := by
        simp
        rw [union_comm _ ({y} ∪ {z}), union_assoc, union_comm {z} s]
        rfl
      rw [this]
      exact hz₂'
  }
  tfae_have 3 → 1
  { exact weakerExchangeAxiom_exchangeAxiom }
  tfae_finish

/-- Add to `exchange_axioms_TFAE`? -/
theorem exchange_property_bases_card_iff {Sys : Finset (Finset α)} :
    exchangeAxiom Sys ↔ (∀ a : Finset α,
      ∀ b₁ ∈ SetSystem.bases Sys a, ∀ b₂ ∈ SetSystem.bases Sys a,
      b₁.card = b₂.card) := by
  constructor <;> intro h
  . intro a b₁ hb₁ b₂ hb₂
    by_contra' h'
    apply (lt_or_gt_of_ne h').elim <;> intro h' <;> simp [SetSystem.bases] at hb₁ hb₂
    . let ⟨x, hx₁, hx₂⟩ := h hb₂.1 hb₁.1 h'
      simp at hx₁
      exact (hb₁.2.2 x (fun h => hx₁.2 h)).elim (fun h => h (hb₂.2.1 hx₁.1)) (fun h => h hx₂)
    . let ⟨x, hx₁, hx₂⟩ := h hb₁.1 hb₂.1 h'
      simp at hx₁
      exact (hb₂.2.2 x (fun h => hx₁.2 h)).elim (fun h => h (hb₁.2.1 hx₁.1)) (fun h => h hx₂)
  . intro s₁ hs₁ s₂ hs₂ hs
    by_contra' h'
    have hs₂' : s₂ ∈ SetSystem.bases Sys (s₁ ∪ s₂) := by
      simp [SetSystem.bases, hs₂, Finset.subset_union_right]
      intro a ha
      exact (em (a ∈ s₁)).elim
        (fun h => Or.inr (h' a (by simp [ha, h])))
        (fun h => Or.inl (by simp [ha, h]))
    have ⟨b, hb₁, hb₂⟩ := exists_bases_containing_feasible_set hs₁ (Finset.subset_union_left s₁ s₂)
    have := h _ _ hs₂' _ hb₁
    rw [this] at hs
    have := Finset.eq_of_subset_of_card_le hb₂
      (by simp at hs; simp [hs, Nat.le_of_lt] : b.card ≤ s₁.card)
    simp [← this] at hs

end ExchangeAxioms

/-- Language version of greedoid. -/
structure GreedoidLanguage (α : Type _) [Fintype α] where
  /-- `language` is a finite sequence of simple words. -/
  language : Finset (List α)
  /-- Every words of the `language` are simple, i.e., no words contains duplicates. -/
  simple : ∀ w ∈ language, w.Nodup
  /-- `language` contains an empty word. -/
  contains_empty : [] ∈ language
  /-- For every word `w = w₂ ++ w₁ ∈ language`, `w₁ ∈ language` also holds. -/
  contains_prefix : ∀ w₁ w₂ : List α, w₂ ++ w₁ ∈ language → w₁ ∈ language
  /-- Exchange Axiom -/
  exchangeAxiom : {w₁ : List α} → w₁ ∈ language → {w₂ : List α} → w₂ ∈ language →
    w₁.length > w₂.length → ∃ x ∈ w₁, x :: w₂ ∈ language

/-- List of axioms in `GreedoidLanguage` -/
def greedoidLanguageAxiom {α : Type _} (Lang : Finset (List α)) :=
  (∀ w ∈ Lang, w.Nodup) ∧
  ([] ∈ Lang) ∧
  (∀ w₁ w₂ : List α, w₂ ++ w₁ ∈ Lang → w₁ ∈ Lang) ∧
  ({w₁ : List α} → w₁ ∈ Lang → {w₂ : List α} → w₂ ∈ Lang →
    w₁.length > w₂.length → ∃ x ∈ w₁, x :: w₂ ∈ Lang)

instance {α : Type _} [Fintype α] [DecidableEq α] :
    DecidablePred (@greedoidLanguageAxiom α) := fun Lang =>
  if h₁ : ∀ w ∈ Lang, w.Nodup
  then if h₂ : [] ∈ Lang
    then if h₃ : ∀ w ∈ Lang, ∀ w' ∈ w.tails, w' ∈ Lang
      then if h₄ : {w₁ : List α} → w₁ ∈ Lang → {w₂ : List α} → w₂ ∈ Lang → w₁.length > w₂.length →
          ∃ x ∈ w₁, x :: w₂ ∈ Lang
        then isTrue (by
          simp_all [greedoidLanguageAxiom]
          intro w₁ w₂ h
          exact h₃ (w₂ ++ w₁) h w₁ (by simp))
        else isFalse (by simp_all [greedoidLanguageAxiom])
      else isFalse (by
        simp [greedoidLanguageAxiom]
        intro _ _ h₃'
        simp at h₃
        let ⟨w, hw, ⟨w', hw'₁, hw'₂⟩⟩ := h₃
        exists w
        simp_all
        exists w'
        simp [hw'₁, hw'₂]
        apply hw'₂
        let ⟨w'', hw''⟩ := hw'₁
        apply h₃' _ w''
        rw [hw'']
        exact hw)
    else isFalse (by simp [greedoidLanguageAxiom, h₂])
  else isFalse (by simp [greedoidLanguageAxiom, h₁])

protected theorem GreedoidLanguage.eq_of_veq {α : Type _} [Fintype α] :
    ∀ {L₁ L₂ : GreedoidLanguage α}, L₁.language = L₂.language → L₁ = L₂
  | ⟨l₁, _, _, _, _⟩, ⟨l₂, _, _, _, _⟩, h => by cases h; rfl

instance {α : Type _} [Fintype α] [DecidableEq α] :
    DecidableEq (GreedoidLanguage α) := fun L₁ L₂ =>
  if h : L₁.language = L₂.language
  then isTrue (GreedoidLanguage.eq_of_veq h)
  else isFalse (fun h' => h (by simp only [h']))

theorem greedoidLanguageAxiom_greedoidLangauge {α : Type _} [Fintype α] {L : GreedoidLanguage α} :
    greedoidLanguageAxiom L.language :=
  ⟨L.simple, L.contains_empty, L.contains_prefix, L.exchangeAxiom⟩

instance {α : Type _} [Fintype α] [DecidableEq α] : Fintype (GreedoidLanguage α) where
  elems :=
    let simple_lists : Finset (List α) :=
      (Finset.univ.powerset.image fun s => s.val.lists).biUnion id
    let simple_languages : Finset (Finset (List α)) :=
      simple_lists.powerset.filter greedoidLanguageAxiom
    simple_languages.attach.map ⟨fun Lang => ⟨Lang.val, fun _ hw => by
        let ⟨val, prop⟩ := Lang; simp only at hw; simp at prop; exact prop.2.1 _ hw, by
        let ⟨val, prop⟩ := Lang; simp only; simp at prop; exact prop.2.2.1, by
        let ⟨val, prop⟩ := Lang; simp only; simp at prop; exact prop.2.2.2.1, by
        let ⟨val, prop⟩ := Lang; simp only; simp at prop; exact fun _ => prop.2.2.2.2⟩,
      fun L₁ L₂ hL => by simp only [GreedoidLanguage.mk.injEq] at hL; exact Subtype.ext hL⟩
  complete := by
    intro L; simp; exists L.language; simp [greedoidLanguageAxiom_greedoidLangauge]
    intro w hw; simp; exists w.toFinset; simp [L.simple _ hw, List.Nodup.dedup]

instance {α : Type _} [Fintype α] [DecidableEq α] {L : GreedoidLanguage α} :
    Language.Hereditary L.language where
  simple := L.simple
  contains_empty := L.contains_empty
  contains_prefix := L.contains_prefix

/-- Set System version of greedoid. -/
structure GreedoidSystem (α : Type _) [Fintype α] [DecidableEq α] where
  /-- `feasible_set` contains sets which are feasible. -/
  feasible_set : Finset (Finset α)
  /-- `feasible_set` contains an empty set. -/
  contains_empty : ∅ ∈ feasible_set
  /-- `feasible_set` is accessible. -/
  accessible : ∀ s ∈ feasible_set, s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ feasible_set
  /-- Exchange Axiom -/
  exchangeAxiom : exchangeAxiom feasible_set

/-- List of axioms in `GreedoidSystem` -/
def greedoidSystemAxiom {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) :=
  ∅ ∈ Sys ∧ (∀ s ∈ Sys, s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ Sys) ∧ exchangeAxiom Sys

instance {α : Type _} [DecidableEq α] :
    DecidablePred (@greedoidSystemAxiom α _) := fun Sys =>
  if h₁ : ∅ ∈ Sys
  then if h₂ : ∀ s ∈ Sys, s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ Sys
    then if h₃ : exchangeAxiom Sys
      then isTrue (by simp_all [greedoidSystemAxiom])
      else isFalse (by simp [greedoidSystemAxiom, h₃])
    else isFalse (by simp [greedoidSystemAxiom, h₂])
  else isFalse (by simp [greedoidSystemAxiom, h₁])

protected theorem GreedoidSystem.eq_of_veq {α : Type _} [Fintype α] [DecidableEq α] :
    ∀ {S₁ S₂ : GreedoidSystem α}, S₁.feasible_set = S₂.feasible_set → S₁ = S₂
  | ⟨s₁, _, _, _⟩, ⟨s₂, _, _, _⟩, h => by cases h; rfl

instance {α : Type _} [Fintype α] [DecidableEq α] :
    DecidableEq (GreedoidSystem α) := fun S₁ S₂ =>
  if h : S₁.feasible_set = S₂.feasible_set
  then isTrue (GreedoidSystem.eq_of_veq h)
  else isFalse (fun h' => h (by simp only [h']))

theorem greedoidSystemAxiom_greedoidSystem {α : Type _} [Fintype α] [DecidableEq α]
  {S : GreedoidSystem α} :
    greedoidSystemAxiom S.feasible_set :=
  ⟨S.contains_empty, S.accessible, S.exchangeAxiom⟩

instance {α : Type _} [Fintype α] [DecidableEq α] : Fintype (GreedoidSystem α) where
  elems := ((@Finset.univ α _).powerset.powerset.filter greedoidSystemAxiom).attach.map
    ⟨fun Sys => ⟨Sys.val, by
        let ⟨val, prop⟩ := Sys; simp only; simp at prop; exact prop.1, fun _ h₁ h₂ => by
        let ⟨val, prop⟩ := Sys; simp only; simp at prop h₁; exact prop.2.1 _ h₁ h₂,
        fun {a} b {c} d e => by
        let ⟨val, prop⟩ := Sys; simp only; simp at prop a c b d; exact prop.2.2 b d e⟩,
      fun S₁ S₂ hS => by simp only [GreedoidSystem.mk.injEq] at hS; exact Subtype.ext hS⟩
  complete := by intro S; simp; exists S.feasible_set; simp [greedoidSystemAxiom_greedoidSystem]

instance {α : Type _} [Fintype α] [DecidableEq α] {S : GreedoidSystem α} :
    SetSystem.Accessible S.feasible_set where
  contains_empty := S.contains_empty
  accessible := S.accessible

/- --------------------------------------------------------- -/
/- TODO: use `toAssociatedSystem` and `toHereditaryLanguage` -/
/- --------------------------------------------------------- -/

/-- Checks if the converted set equals the feasible set.

    `feasible_set = {↑w | w ∈ language}` -/
protected def GreedoidLanguage.fromLanguageToSystem' {α : Type _} [Fintype α] [DecidableEq α]
  (L : GreedoidLanguage α) := Language.toAssociatedSetSystem L.language

instance AccessibleLanguageToSystem' {α : Type _} [Fintype α] [DecidableEq α]
  (L : GreedoidLanguage α) :
    SetSystem.Accessible L.fromLanguageToSystem' :=
  SetSystem.toAssociatedSetSystem_Accessible L.language

theorem greedoidSystemAxiom_fromLanguageToSystem' {α : Type _} [Fintype α] [DecidableEq α]
  {L : GreedoidLanguage α} :
    greedoidSystemAxiom L.fromLanguageToSystem' := by
  have := AccessibleLanguageToSystem' L
  simp only [greedoidSystemAxiom, this.contains_empty, ne_eq, true_and]
  apply And.intro (fun _ h₁ h₂ => this.accessible _ h₁ h₂)
  simp [exchangeAxiom, GreedoidLanguage.fromLanguageToSystem', Language.toAssociatedSetSystem]
  intro w₁ hw₁ w₂ hw₂ hw
  have ⟨x, hx₁, hx₂⟩ := L.exchangeAxiom hw₁ hw₂ (by
    simp [List.card_toFinset, List.dedup_eq_self.mpr (L.simple _ hw₁),
      List.dedup_eq_self.mpr (L.simple _ hw₂)] at hw
    exact hw)
  have hx₃ := L.simple _ hx₂
  simp only [List.nodup_cons] at hx₃
  exists x
  simp only [hx₁, hx₃, true_and]
  exists (x :: w₂)
  simp only [hx₂, true_and]
  rw [Finset.union_comm, ← Finset.insert_eq]
  simp only [List.toFinset_cons, List.mem_toFinset]

theorem fromLanguageToSystem'_eq {α : Type _} [Fintype α] [DecidableEq α]
  {L₁ L₂ : GreedoidLanguage α} (hL : L₁.fromLanguageToSystem' = L₂.fromLanguageToSystem') :
    L₁ = L₂ := by
  let ⟨Lang₁, hLang₁₁, hLang₁₂, hLang₁₃, hLang₁₄⟩ := L₁
  let ⟨Lang₂, hLang₂₁, hLang₂₂, hLang₂₃, hLang₂₄⟩ := L₂
  simp_all [GreedoidLanguage.fromLanguageToSystem', Language.toAssociatedSetSystem]
  ext w; constructor <;> intro h <;> induction' w with head w ih <;> simp only [hLang₁₂, hLang₂₂]
  . have hhead : head ∉ w := by have := hLang₁₁ _ h; simp at this; exact this.1
    have hw₁ := ih (hLang₁₃ w [head] (by simp only [List.singleton_append, h]))
    have ⟨w', hw'₁, hw'₂⟩ : ∃ w' ∈ Lang₂, w'.toFinset = w.toFinset ∪ {head} := by
      have ⟨w', hw'₁, hw'₃⟩ : ∃ w' ∈ Lang₂, w'.toFinset = (head :: w).toFinset := by
        rw [← Finset.mem_image, ← hL, Finset.mem_image]; exists (head :: w)
      exists w'
      simp only [List.toFinset_cons] at hw'₃
      simp only [hw'₁, hw'₃, hhead, Finset.insert_eq, Finset.union_comm]
    have ⟨head', hhead'₁, hhead'₂⟩ := hLang₂₄ hw'₁ hw₁ (by
      rw [Finset.union_comm, ← Finset.insert_eq] at hw'₂
      rw [← List.toFinset_card_of_nodup (hLang₂₁ _ hw'₁),
        ← List.toFinset_card_of_nodup (hLang₂₁ _ hw₁), hw'₂]
      simp [hhead])
    have : head = head' := by
      have : head' ∉ w := by have := hLang₂₁ _ hhead'₂; rw [List.nodup_cons] at this; tauto
      rw [← List.mem_toFinset, hw'₂, Finset.union_comm, ← Finset.insert_eq,
        Finset.mem_insert, List.mem_toFinset] at hhead'₁; tauto
    rw [this]; exact hhead'₂
  . have hhead : head ∉ w := by have := hLang₂₁ _ h; simp at this; exact this.1
    have hw₁ := ih (hLang₂₃ w [head] (by simp only [List.singleton_append, h]))
    have ⟨w', hw'₁, hw'₂⟩ : ∃ w' ∈ Lang₁, w'.toFinset = w.toFinset ∪ {head} :=  by
      have ⟨w', hw'₁, hw'₃⟩ : ∃ w' ∈ Lang₁, w'.toFinset = (head :: w).toFinset := by
        rw [← Finset.mem_image, hL, Finset.mem_image]; exists (head :: w)
      exists w'
      simp only [List.toFinset_cons] at hw'₃
      simp only [hw'₁, hw'₃, hhead, Finset.insert_eq, Finset.union_comm]
    have ⟨head', hhead'₁, hhead'₂⟩ := hLang₁₄ hw'₁ hw₁ (by
      rw [Finset.union_comm, ← Finset.insert_eq] at hw'₂
      rw [← List.toFinset_card_of_nodup (hLang₁₁ _ hw'₁),
        ← List.toFinset_card_of_nodup (hLang₁₁ _ hw₁), hw'₂]
      simp [hhead])
    have : head = head' := by
      have : head' ∉ w := by have := hLang₁₁ _ hhead'₂; rw [List.nodup_cons] at this; tauto
      rw [← List.mem_toFinset, hw'₂, Finset.union_comm, ← Finset.insert_eq,
        Finset.mem_insert, List.mem_toFinset] at hhead'₁; tauto
    rw [this]; exact hhead'₂

/-- Converts language to system. -/
protected def GreedoidLanguage.fromLanguageToSystem {α : Type _} [Fintype α] [DecidableEq α]
    (L : GreedoidLanguage α) : GreedoidSystem α :=
  ⟨L.fromLanguageToSystem',
    greedoidSystemAxiom_fromLanguageToSystem'.1,
    greedoidSystemAxiom_fromLanguageToSystem'.2.1,
    greedoidSystemAxiom_fromLanguageToSystem'.2.2⟩

theorem fromLanguageToSystem_eq {α : Type _} [Fintype α] [DecidableEq α]
  {L₁ L₂ : GreedoidLanguage α} (hL : L₁.fromLanguageToSystem = L₂.fromLanguageToSystem) :
    L₁ = L₂ := by
  apply fromLanguageToSystem'_eq
  simp [GreedoidLanguage.fromLanguageToSystem] at hL
  exact hL

/-- Checks if the converted language equals the language.

    `language = {w | underlying set of every prefix of w is feasible}` -/
protected def GreedoidSystem.fromSystemToLanguage' {α : Type _} [Fintype α] [DecidableEq α]
  (S : GreedoidSystem α) : Finset (List α) := SetSystem.toHereditaryLanguage S.feasible_set

instance HereditarySystemToLanguage' {α : Type _} [Fintype α] [DecidableEq α]
  (S : GreedoidSystem α) :
    Language.Hereditary S.fromSystemToLanguage' :=
  SetSystem.toHereditaryLanguage_Hereditary S.feasible_set

theorem greedoidLanguageAxiom_fromSystemToLanguage' {α : Type _} [Fintype α] [DecidableEq α]
  {S : GreedoidSystem α} :
    greedoidLanguageAxiom S.fromSystemToLanguage' := by
  have := HereditarySystemToLanguage' S
  simp only [greedoidLanguageAxiom, this.contains_empty, gt_iff_lt, true_and]
  apply And.intro this.simple (And.intro (fun _ _ h => this.contains_prefix _ _ h) _)
  simp [GreedoidSystem.fromSystemToLanguage', SetSystem.toHereditaryLanguage]
  intro w₁ s₁ hs₁₁ hs₁₂ _ w₂ s₂ hs₂₁ hs₂₂ hw₂ hw
  have w₁_nodup : w₁.Nodup := Multiset.coe_nodup.mp (hs₁₂ ▸ s₁.nodup)
  have w₂_nodup : w₂.Nodup := Multiset.coe_nodup.mp (hs₂₂ ▸ s₂.nodup)
  have s₁_eq_w₁_toFinset : s₁ = w₁.toFinset := by
    rw [← List.toFinset_eq w₁_nodup]
    apply Finset.eq_of_veq
    exact hs₁₂
  have s₂_eq_w₂_toFinset : s₂ = w₂.toFinset := by
    rw [← List.toFinset_eq w₂_nodup]
    apply Finset.eq_of_veq
    exact hs₂₂
  have ⟨x, hx₁, hx₂⟩ := S.exchangeAxiom hs₁₁ hs₂₁ (by
    simp only [s₁_eq_w₁_toFinset, s₂_eq_w₂_toFinset, w₁_nodup, w₂_nodup,
      List.toFinset_card_of_nodup, hw])
  exists x
  rw [s₁_eq_w₁_toFinset, s₂_eq_w₂_toFinset] at hx₁
  have x_notin_w₂ : x ∉ w₂ := by simp_all
  apply And.intro (by simp_all) (And.intro _ (And.intro _ (fun _ h => hw₂ _ h)))
  . exists w₂.toFinset ∪ {x}
    apply And.intro (s₂_eq_w₂_toFinset ▸ hx₂)
    rw [Finset.union_comm, ← Finset.insert_eq]
    simp [x_notin_w₂, w₂_nodup, List.Nodup.dedup]
  . rw [Finset.union_comm, ← Finset.insert_eq, s₂_eq_w₂_toFinset] at hx₂
    exact hx₂

theorem fromSystemToLanguage'_eq {α : Type _} [Fintype α] [DecidableEq α]
  {S₁ S₂ : GreedoidSystem α} (hS : S₁.fromSystemToLanguage' = S₂.fromSystemToLanguage') :
    S₁ = S₂ := by
  simp_all [GreedoidSystem.fromSystemToLanguage']
  apply GreedoidSystem.eq_of_veq
  ext s; constructor <;> intro hs₁ <;> by_cases hs₂ : s = ∅ <;>
    simp only [hs₂, S₂.contains_empty, S₁.contains_empty]
  . apply SetSystem.induction_on_accessible s hs₁ S₂.contains_empty
    intro a s _ _ hs₂ _
    have ⟨w, hw₁, hw₂⟩ := SetSystem.mem_toHereditaryLanguage hs₂
    rw [hS] at hw₁
    simp [SetSystem.toHereditaryLanguage] at hw₁
    exact hw₂ ▸ hw₁.2 w List.suffix_rfl
  . apply SetSystem.induction_on_accessible _ hs₁ S₁.contains_empty
    intro a s _ _ hs₂ _
    have ⟨w, hw₁, hw₂⟩ := SetSystem.mem_toHereditaryLanguage hs₂
    rw [← hS] at hw₁
    simp [SetSystem.toHereditaryLanguage] at hw₁
    exact hw₂ ▸ hw₁.2 w List.suffix_rfl

/-- Converts system to language. -/
protected def GreedoidSystem.fromSystemToLanguage {α : Type _} [Fintype α] [DecidableEq α]
    (S : GreedoidSystem α) : GreedoidLanguage α :=
  ⟨S.fromSystemToLanguage',
    greedoidLanguageAxiom_fromSystemToLanguage'.1,
    greedoidLanguageAxiom_fromSystemToLanguage'.2.1,
    greedoidLanguageAxiom_fromSystemToLanguage'.2.2.1,
    greedoidLanguageAxiom_fromSystemToLanguage'.2.2.2⟩

theorem fromSystemToLanguage_eq {α : Type _} [Fintype α] [DecidableEq α]
  {S₁ S₂ : GreedoidSystem α} (hS : S₁.fromSystemToLanguage = S₂.fromSystemToLanguage) :
    S₁ = S₂ := by
  apply fromSystemToLanguage'_eq
  simp [GreedoidSystem.fromSystemToLanguage] at hS
  exact hS

@[simp]
theorem fromSystemToLanguage_fromLanguageToSystem_eq {α : Type _} [Fintype α] [DecidableEq α]
    {S : GreedoidSystem α} : S.fromSystemToLanguage.fromLanguageToSystem = S := by
  simp [GreedoidLanguage.fromLanguageToSystem, GreedoidSystem.fromSystemToLanguage,
    GreedoidLanguage.fromLanguageToSystem', GreedoidSystem.fromSystemToLanguage',
    Language.toAssociatedSetSystem, SetSystem.toHereditaryLanguage]
  apply GreedoidSystem.eq_of_veq
  simp; ext x; constructor <;> intro h
  . simp at h
    have ⟨a, ⟨_, ha₂⟩, ha₃⟩ := h
    exact ha₃ ▸ ha₂ _ List.suffix_rfl
  . apply SetSystem.induction_on_accessible x h (by simp [S.contains_empty])
    simp
    intro a s₁ hs₁₁ hs₁₂ hs₁₃ w s₂ hs₂₁ hs₂₂ hw₁ hw₂
    exists a :: w
    simp_all [Finset.insert_eq, Finset.union_comm]
    have w_nodup : w.Nodup := Multiset.coe_nodup.mp (hs₂₂ ▸ s₂.nodup)
    have a_notin_w : a ∉ w := fun h' => hs₁₁ (by rw [← hw₂]; simp only [List.mem_toFinset, h'])
    constructor
    . exists s₁ ∪ {a}
      simp only [true_and, hs₁₃]
      rw [Finset.union_comm, ← Finset.insert_eq, ← hw₂]
      have w_nodup : w.Nodup := Multiset.coe_nodup.mp (hs₂₂ ▸ s₂.nodup)
      have a_notin_w : a ∉ w := fun h' => hs₁₁ (by rw [← hw₂]; simp only [List.mem_toFinset, h'])
      simp [Multiset.coe_nodup, w_nodup, a_notin_w, List.Nodup.dedup]
    . intro w' hw'
      rw [List.suffix_cons_iff] at hw'
      apply hw'.elim <;> intro hw'
      . rw [hw']
        simp [Finset.union_comm, ← Finset.insert_eq, Multiset.coe_nodup,
          w_nodup, a_notin_w, List.Nodup.dedup, hw₂]
        rw [Finset.insert_eq, Finset.union_comm]
        exact hs₁₃
      . exact hw₁ _ hw'

@[simp]
theorem fromLanguageToSystem_fromSystemToLanguage_eq {α : Type _} [Fintype α] [DecidableEq α]
    {L : GreedoidLanguage α} : (L.fromLanguageToSystem).fromSystemToLanguage = L := by
  simp [GreedoidLanguage.fromLanguageToSystem, GreedoidSystem.fromSystemToLanguage,
    GreedoidLanguage.fromLanguageToSystem', GreedoidSystem.fromSystemToLanguage']
  apply GreedoidLanguage.eq_of_veq
  simp only; symm
  rw [hereditary_language_lemma]
  intro w₁ hw₁ w₂ hw₂ x hx hw
  have x_notin_w₂ : x ∉ w₂ := by simp at hx ; simp only [hx]
  have ⟨x', hx'₁, hx'₂⟩ := L.exchangeAxiom hw₁ hw₂ (by
    rw [← List.toFinset_card_of_nodup (L.simple _ hw₁),
      ← List.toFinset_card_of_nodup (L.simple _ hw₂), hw]
    simp_arith [x_notin_w₂])
  have : x' = x := by
    simp at hx
    rw [Finset.union_comm, ← Finset.insert_eq, Finset.ext_iff] at hw
    simp only [List.mem_toFinset, Finset.mem_insert] at hw
    apply ((hw x').mp hx'₁).elim <;> intro h <;> try trivial
    have := L.simple _ hx'₂
    rw [List.nodup_cons] at this
    tauto
  exact this ▸ hx'₂

/-- `relatedLanguageSystem` checks if a given language and system are related to each other.
    That is, given that the language is hereditary,

    1. `feasible_set = {↑w | w ∈ language}`
    2. `language = {w | underlying set of every prefix of w is feasible}` -/
protected def Greedoid.relatedLanguageSystem' {α : Type _} [Fintype α] [DecidableEq α]
  (L : GreedoidLanguage α) (S : GreedoidSystem α) : Prop :=
  S.feasible_set = L.fromLanguageToSystem' ∧ L.language = S.fromSystemToLanguage'

protected def Greedoid.relatedLanguageSystem {α : Type _} [Fintype α] [DecidableEq α]
  (L : GreedoidLanguage α) (S : GreedoidSystem α) : Prop :=
  S = L.fromLanguageToSystem ∧ L = S.fromSystemToLanguage

@[simp]
theorem relatedLanguageSystem'_iff_relatedLanguageSystem {α : Type _} [Fintype α] [DecidableEq α]
  {L : GreedoidLanguage α} {S : GreedoidSystem α} :
    Greedoid.relatedLanguageSystem' L S ↔ Greedoid.relatedLanguageSystem L S := by
  simp [Greedoid.relatedLanguageSystem', Greedoid.relatedLanguageSystem]
  constructor <;> rintro ⟨h₁, h₂⟩ <;>
  simp [GreedoidLanguage.fromLanguageToSystem, GreedoidSystem.fromSystemToLanguage] at * <;>
  constructor
  . apply GreedoidSystem.eq_of_veq; exact h₁
  . apply GreedoidLanguage.eq_of_veq; exact h₂
  . simp only [h₁]
  . simp only [h₂]

theorem relatedLanguageSystem_eq {α : Type _} [Fintype α] [DecidableEq α]
  {L₁ L₂ : GreedoidLanguage α} {S₁ S₂ : GreedoidSystem α}
  (h₁ : Greedoid.relatedLanguageSystem L₁ S₁)
  (h₂ : Greedoid.relatedLanguageSystem L₂ S₂) :
    L₁ = L₂ ↔ S₁ = S₂ :=
  ⟨fun h => fromSystemToLanguage_eq ((h ▸ h₁.2) ▸ h₂.2),
   fun h => fromLanguageToSystem_eq ((h ▸ h₁.1) ▸ h₂.1)⟩

theorem relatedLanguageSystem_of_fromLanguageToSystem {α : Type _} [Fintype α] [DecidableEq α]
  {L : GreedoidLanguage α} : Greedoid.relatedLanguageSystem L L.fromLanguageToSystem := by
  simp [Greedoid.relatedLanguageSystem]

theorem relatedLanguageSystem_of_fromSystemToLanguage {α : Type _} [Fintype α] [DecidableEq α]
  {S : GreedoidSystem α} : Greedoid.relatedLanguageSystem S.fromSystemToLanguage S := by
  simp [Greedoid.relatedLanguageSystem]

theorem toFinset_mem_greedoidSystem_of_mem_greedoidLanguage {α : Type _} [Fintype α]
  [DecidableEq α] {L : GreedoidLanguage α} {S : GreedoidSystem α}
  (hrelated : Greedoid.relatedLanguageSystem L S) {w : List α} (hw : w ∈ L.language) :
    w.toFinset ∈ S.feasible_set := by
  simp only [(relatedLanguageSystem'_iff_relatedLanguageSystem.mpr hrelated).1,
    GreedoidLanguage.fromLanguageToSystem', Language.toAssociatedSetSystem, Finset.mem_image]
  exists w

theorem exists_word_mem_greedoidLanguage_of_mem_greedoidSystem {α : Type _} [Fintype α]
  [DecidableEq α] {L : GreedoidLanguage α} {S : GreedoidSystem α}
  (hrelated : Greedoid.relatedLanguageSystem L S) {s : Finset α} (hs : s ∈ S.feasible_set) :
    ∃ w ∈ L.language, w.toFinset = s := by
  simp only [(relatedLanguageSystem'_iff_relatedLanguageSystem.mpr hrelated).1,
    GreedoidLanguage.fromLanguageToSystem', Language.toAssociatedSetSystem, Finset.mem_image] at hs
  exact hs

/-- Merging of language and system version of greedoid.
    This will (potentially) help `Greedoid` cover theorems written in
    both language and systems. -/
structure Greedoid (α : Type _) [Fintype α] [DecidableEq α] where
  /-- Greedoid as a language. -/
  language : GreedoidLanguage α
  /-- Greedoid as a system. -/
  system : GreedoidSystem α
  /-- `language` and `system` are related. -/
  related : Greedoid.relatedLanguageSystem language system

/-- Definition of `Finset` in `Greedoid` -/
protected def Greedoid.finsetMem {α : Type _} [Fintype α] [DecidableEq α]
  (s : Finset α) (G : Greedoid α) := s ∈ G.system.feasible_set

/-- Definition of `List` (or equivalently, `Word`) in `Greedoid` -/
protected def Greedoid.wordMem {α : Type _} [Fintype α] [DecidableEq α]
  (w : List α) (G : Greedoid α) := w ∈ G.language.language

@[inherit_doc] infix:50 " ∈ₛ " => Greedoid.finsetMem
/-- Negated version of `∉ₛ` -/
infix:50 " ∉ₛ " => fun s G => ¬ (Greedoid.finsetMem s G)
@[inherit_doc] infix:50 " ∈ₗ " => Greedoid.wordMem
/-- Negated version of `∉ₗ` -/
infix:50 " ∉ₗ " => fun w G => ¬ (Greedoid.wordMem w G)
/-- Prefer `∈ₛ` for greedoids. -/
instance {α : Type _} [Fintype α] [DecidableEq α] :
  Membership (Finset α) (Greedoid α) := ⟨Greedoid.finsetMem⟩

namespace Greedoid

open List Finset Multiset

variable {α : Type _} [Fintype α] [DecidableEq α] {G : Greedoid α}

theorem eq_of_veq : ∀ {G₁ G₂ : Greedoid α},
  G₁.language = G₂.language → G₁.system = G₂.system → G₁ = G₂
  | ⟨l₁, s₁, _⟩, ⟨l₂, s₂, _⟩, h₁, h₂ => by cases h₁; cases h₂; rfl

theorem eq_of_leq : ∀ {G₁ G₂ : Greedoid α}, G₁.language = G₂.language → G₁ = G₂ := by
  intro G₁ G₂ hl
  apply eq_of_veq hl
  rw [← relatedLanguageSystem_eq G₁.related G₂.related]
  exact hl

theorem eq_of_seq : ∀ {G₁ G₂ : Greedoid α}, G₁.system = G₂.system → G₁ = G₂ := by
  intro G₁ G₂ hs
  apply eq_of_veq _ hs
  rw [relatedLanguageSystem_eq G₁.related G₂.related]
  exact hs

theorem language_injective : Function.Injective (language : Greedoid α → GreedoidLanguage α) :=
  fun _ _ => eq_of_leq

theorem system_injective : Function.Injective (system : Greedoid α → GreedoidSystem α) :=
  fun _ _ => eq_of_seq

@[simp]
theorem language_inj {G₁ G₂ : Greedoid α} : G₁.language = G₂.language ↔ G₁ = G₂ :=
  language_injective.eq_iff

@[simp]
theorem system_inj {G₁ G₂ : Greedoid α} : G₁.system = G₂.system ↔ G₁ = G₂ :=
  system_injective.eq_iff

@[coe]
def ofGreedoidLanguage : GreedoidLanguage α → Greedoid α :=
  fun L => ⟨L, L.fromLanguageToSystem, relatedLanguageSystem_of_fromLanguageToSystem⟩

@[coe]
def ofGreedoidSystem : GreedoidSystem α → Greedoid α :=
  fun S => ⟨S.fromSystemToLanguage, S, relatedLanguageSystem_of_fromSystemToLanguage⟩

@[simp]
theorem ofGreedoidLanguage_eq : ofGreedoidLanguage G.language = G := by rw [← language_inj]; rfl

@[simp]
theorem ofGreedoidSystem_eq : ofGreedoidSystem G.system = G := by rw [← system_inj]; rfl

instance : DecidableEq (Greedoid α) := fun G₁ G₂ =>
  if h : G₁.language = G₂.language ∨ G₁.system = G₂.system
  then isTrue (h.elim
    (fun h => eq_of_veq h ((relatedLanguageSystem_eq G₁.related G₂.related).mp h))
    (fun h => eq_of_veq ((relatedLanguageSystem_eq G₁.related G₂.related).mpr h) h))
  else isFalse (fun h' => h (Or.inl (h' ▸ rfl)))

instance : Fintype (Greedoid α) where
  elems := (@Finset.univ (GreedoidLanguage α) _).map
    ⟨fun L => ofGreedoidLanguage L, fun _ _ hL => language_inj.mpr hL⟩
  complete G := by
    simp only [Finset.mem_map, mem_univ, Function.Embedding.coeFn_mk]
    exists G.language; simp only [ofGreedoidLanguage_eq]

section Membership

theorem system_feasible_set_mem_mem {s : Finset α} : s ∈ G.system.feasible_set ↔ s ∈ G := by rfl

theorem system_feasible_set_mem_memₛ {s : Finset α} : s ∈ G.system.feasible_set ↔ s ∈ₛ G := by rfl

theorem language_language_mem_memₗ {w : List α} : w ∈ G.language.language ↔ w ∈ₗ G := by rfl

theorem emptyset_finsetMem : (∅ : Finset α) ∈ₛ G := G.system.contains_empty

theorem nil_wordMem : ([] : List α) ∈ₗ G := G.language.contains_empty

theorem emptyset_mem : (∅ : Finset α) ∈ G := G.system.contains_empty

theorem nil_toFinset_mem : [].toFinset ∈ G := G.system.contains_empty

theorem wordMem_nodup {w : List α} (hw : w ∈ₗ G) : w.Nodup := G.language.simple _ hw

@[simp]
theorem finsetMem_mem_iff {s : Finset α} :
    s ∈ G ↔ s ∈ₛ G := by rfl

theorem word_mem_language_toFinset_mem {w : List α} (hw : w ∈ₗ G) :
    w.toFinset ∈ₛ G :=
  toFinset_mem_greedoidSystem_of_mem_greedoidLanguage G.related hw

theorem finset_feasible_exists_word {s : Finset α} (hs : s ∈ₛ G) :
    ∃ w : List α, w ∈ₗ G ∧ w.toFinset = s := by
  have := exists_word_mem_greedoidLanguage_of_mem_greedoidSystem G.related hs
  simp only [Greedoid.wordMem, this]

theorem finset_feasible_exists_feasible_ssubset {s : Finset α}
  (hs₁ : s ∈ₛ G) (hs₂ : s ≠ ∅) :
    ∃ s', s' ⊂ s ∧ (s \ s').card = 1 ∧ s' ∈ₛ G := by
  let ⟨w, hw₁, hw₂⟩ := finset_feasible_exists_word hs₁
  cases w
  case nil => simp_all
  case cons h t =>
    have : (h :: t).Nodup := wordMem_nodup hw₁
    exists t.toFinset
    simp at *
    repeat apply And.intro
    . rw [hw₂]; intro _ _; simp_all
    . intro h'; rw [hw₂] at h'
      have : (h :: t).Nodup := wordMem_nodup hw₁
      simp at this
      apply this.1
      simp at h'
      suffices h₁ : h ∈ t.toFinset by rw [← List.mem_toFinset]; exact h₁
      apply h'
      simp
    . apply And.intro
      . simp [hw₂]
        rw [Finset.card_sdiff]
        . simp_all
        . intro _ _; simp_all
      . have : t ∈ₗ G := G.language.contains_prefix t [h] (by
          simp [Greedoid.wordMem] at hw₁; simp [hw₁])
        simp [this, GreedoidLanguage.fromLanguageToSystem', Greedoid.finsetMem]
        simp [G.related.1, GreedoidLanguage.fromLanguageToSystem',
          GreedoidLanguage.fromLanguageToSystem]
        exists t

end Membership

instance : SetSystem.Accessible G.system.feasible_set where
  contains_empty := G.system.contains_empty
  accessible := by
    intro s hs₁ hs₂
    induction s using Finset.induction_on
    . simp at hs₂
    . clear hs₂
      let ⟨w, hw₁, hw₂⟩ := finset_feasible_exists_word hs₁
      cases w
      case nil => simp_all
      case cons h t =>
        exists h
        have := wordMem_nodup hw₁
        simp at this
        simp [hw₂, Finset.insert_sdiff_of_mem]
        have ht := G.language.contains_prefix _ [h] hw₁
        rw [Finset.sdiff_singleton_eq_self]
        . rw [G.related.1]
          simp [GreedoidLanguage.fromLanguageToSystem', GreedoidLanguage.fromLanguageToSystem]
          exists t
        . simp [this.1]

theorem weakExchangeAxiom : weakExchangeAxiom G.system.feasible_set := by
  apply (exchange_axioms_TFAE.out 0 1).mp
  exact G.system.exchangeAxiom

theorem weakerExchangeAxiom : weakerExchangeAxiom G.system.feasible_set := by
  apply (exchange_axioms_TFAE.out 0 2).mp
  exact G.system.exchangeAxiom

/-- Greedoid is full if the ground set is feasible. -/
def full (G : Greedoid α) := (@Finset.univ α _) ∈ₛ G

/-- The interval prop is satisfied by matroids, antimatroids, and some greedoids. -/
def interval_property (G : Greedoid α) :=
  {A : Finset α} → A ∈ₛ G →
  {B : Finset α} → B ∈ₛ G →
  {C : Finset α} → C ∈ₛ G →
  A ⊆ B → B ⊆ C → {x : α} → x ∉ C →
  A ∪ {x} ∈ₛ G → C ∪ {x} ∈ₛ G → B ∪ {x} ∈ₛ G

/-- Matroid is an interval greedoid without lower bound. -/
def interval_property_wo_lower_bound (G : Greedoid α) :=
  {A : Finset α} → A ∈ₛ G →
  {B : Finset α} → B ∈ₛ G → A ⊆ B →
  {x : α} → x ∉ B →
  B ∪ {x} ∈ₛ G → A ∪ {x} ∈ₛ G

theorem interval_property_wo_lower_bound_then_interval_property {G : Greedoid α}
    (hG : interval_property_wo_lower_bound G) : interval_property G := by
  intro _ _ _ hB _ hC _ h₂ _ hx _ hCx
  exact hG hB hC h₂ hx hCx

/-- Antimatroid is an interval greedoid without upper bound. -/
def interval_property_wo_upper_bound (G : Greedoid α) :=
  {A : Finset α} → A ∈ₛ G →
  {B : Finset α} → B ∈ₛ G → B ⊆ A →
  {x : α} → x ∉ A →
  B ∪ {x} ∈ₛ G → A ∪ {x} ∈ₛ G

theorem interval_property_wo_upper_bound_then_interval_property
    (hG : interval_property_wo_upper_bound G) : interval_property G := by
  intro _ hA _ hB _ _ h₁ h₂ _ hx hAx _
  exact hG hB hA h₁ (fun h => hx (h₂ h)) hAx

/-- A base of a greedoid. -/
def base (G : Greedoid α) := SetSystem.base G.system.feasible_set

/-- A bases of a given set `s` of a greedoid. -/
def bases (G : Greedoid α) (s : Finset α) := SetSystem.bases G.system.feasible_set s

theorem base_bases_eq : G.base = G.bases (@Finset.univ α _) := SetSystem.base_bases_eq

theorem basis_feasible {s b : Finset α} (hb : b ∈ G.bases s) : b ∈ G.system.feasible_set := by
  simp_all [bases, SetSystem.bases]

theorem basis_def {s b : Finset α} :
    b ∈ G.bases s ↔ (b ∈ₛ G ∧ b ⊆ s ∧ (∀ a ∈ s, a ∉ b → b ∪ {a} ∉ₛ G)) := by
  constructor <;> intro h
  . simp [bases, SetSystem.bases] at h
    apply And.intro h.1 (And.intro h.2.1 _)
    intro _ _ ha₂
    have := h.2.2 _ ha₂
    tauto
  . simp [bases, SetSystem.bases]
    apply And.intro h.1 (And.intro h.2.1 _)
    tauto

theorem bases_nonempty {s : Finset α} : Nonempty (G.bases s) := sorry

theorem bases_card_eq {s : Finset α}
  {b₁ : Finset α} (hb₁ : b₁ ∈ G.bases s)
  {b₂ : Finset α} (hb₂ : b₂ ∈ G.bases s) :
    b₁.card = b₂.card := sorry

theorem basis_of_full_unique (hG : G.full) : ∃! b, b ∈ G.base := by
  exists univ
  sorry

theorem bases_of_full_card (hG : G.full) : G.base.card = 1 := by
  let ⟨_, _⟩ := (Finset.singleton_iff_unique_mem _).mpr (basis_of_full_unique hG)
  simp_all

-- TODO: Move to Rank.lean

/-- A cardinality of largest feasible subset of `s` in `G`. -/
def rank (G : Greedoid α) (s : Finset α) :=
  ((G.system.feasible_set.filter (fun s' => s' ⊆ s)).image (fun t => t.card)).max.unbot (by
    intro h
    simp [Finset.max_eq_bot, filter_eq_empty_iff] at h
    exact h _ G.system.contains_empty (by simp only [empty_subset]))

section rank

variable {s t : Finset α} {x y : α}

theorem rank_eq_bases_card :
    ∀ b ∈ SetSystem.bases G.system.feasible_set s, b.card = G.rank s := by
  by_contra'
  let ⟨b, hb₁, hb₂⟩ := this; clear this
  rw [← lt_or_lt_iff_ne] at hb₂
  apply hb₂.elim <;> intro h <;> clear hb₂ <;> clear hb₂
  . sorry
  . sorry

@[simp]
theorem rank_empty : G.rank ∅ = 0 := by
  simp [rank, Finset.subset_empty, Finset.filter_eq', G.system.contains_empty]

theorem rank_le_card : G.rank s ≤ s.card := sorry

theorem subset_then_rank_le (hs : s ⊆ t) : G.rank s ≤ G.rank t := sorry

theorem local_submodularity
  (h₁ : G.rank s = G.rank (s ∪ {x}))
  (h₂ : G.rank s = G.rank (s ∪ {y})) :
    G.rank (s ∪ {x, y}) = G.rank s := sorry

theorem stronger_local_submodularity_left
  (h₁ : G.rank s = G.rank (s ∩ t))
  (h₂ : G.rank t = G.rank (s ∩ t)) :
    G.rank s = G.rank (s ∪ t) := sorry

theorem stronger_local_submodularity_right
  (h₁ : G.rank s = G.rank (s ∩ t))
  (h₂ : G.rank t = G.rank (s ∩ t)) :
    G.rank t = G.rank (s ∪ t) := by
  simp [h₂, ← h₁, stronger_local_submodularity_left h₁ h₂]

-- TODO: Looking for better name
theorem rank_lt_succ_lt
  (hs₁ : G.rank s < G.rank (s ∪ {x}))
  (hs₂ : G.rank s < G.rank (s ∪ {y})) :
    G.rank s + 1 < G.rank (s ∪ {x, y}) := sorry

theorem rank_of_feasible (hs : s ∈ₛ G) : G.rank s = s.card := sorry

theorem rank_of_infeasible (hs : s ∉ₛ G) : G.rank s < s.card := sorry

@[simp]
theorem rank_eq_card_iff_feasible : G.rank s = s.card ↔ s ∈ₛ G := by
  apply Iff.intro _ (fun h => rank_of_feasible h)
  intro h
  have := mt (@rank_of_infeasible _ _ _ G s)
  simp at this
  apply this
  simp only [h, le_refl]

theorem ssubset_of_feasible_rank (hs : s ∈ₛ G) (h : t ⊂ s) : G.rank t < G.rank s := sorry

/-- List of axioms for rank of greedoid. -/
def greedoidRankAxioms (r : Finset α → ℕ) :=
  (r ∅ = 0) ∧ (∀ s, r s ≤ s.card) ∧ (∀ s t, s ⊆ t → r s ≤ r t) ∧
  (∀ s x y, r s = r (s ∪ {x}) → r s = r (s ∪ {y}) → r s = r (s ∪ {x, y}))

theorem greedoidRankAxioms_unique_greedoid {r : Finset α → ℕ} (hr : greedoidRankAxioms r) :
    ∃! G : Greedoid α, G.rank = r := sorry

/-- Rank function satisfying `greedoidRankAxioms` generates a unique greedoid. -/
protected def rank.toGreedoid (r : Finset α → ℕ) (hr : greedoidRankAxioms r) : Greedoid α :=
  Fintype.choose (fun G => G.rank = r) (greedoidRankAxioms_unique_greedoid hr)

end rank

-- TODO: Move to Closure.lean

/-- Closure of `s` is the largest set which contains `s` and have the same rank with `s`. -/
def closure (G : Greedoid α) (s : Finset α) : Finset α:=
  (@Finset.univ α _).filter (fun x => G.rank (s ∪ {x}) = G.rank s)

section closure

variable {s t : Finset α} {x y : α}

theorem self_subset_closure : s ⊆ G.closure s := by
  simp [closure]
  intro x hx
  have hx : {x} ⊆ s := by simp only [singleton_subset_iff, hx]
  simp [Finset.union_eq_left_iff_subset.mpr hx]

@[simp]
theorem rank_closure_eq_rank_self : G.rank (G.closure s) = G.rank s := sorry

theorem feasible_iff_elem_notin_closure_minus_elem :
    s ∈ₛ G ↔ ∀ x ∈ s, x ∉ G.closure (s \ {x}) := by
  simp [closure]
  constructor <;> intro h
  . intro x hx h'
    have hx : {x} ⊆ s := by simp only [singleton_subset_iff, hx]
    simp [Finset.union_eq_left_iff_subset.mpr hx] at h'
    rw [rank_of_feasible h] at h'
    have := @ssubset_of_feasible_rank _ _ _ G s (s \ {x}) h sorry
    simp [← h', rank_eq_card_iff_feasible.mpr h] at this
  . sorry

theorem closure_eq_of_subset_adj_closure (hst : s ⊆ G.closure t) (hts : t ⊆ G.closure s) :
    G.closure s = G.closure t := sorry

theorem closure_idempotent : G.closure (G.closure s) = G.closure s :=
  closure_eq_of_subset_adj_closure (by simp)
    (Finset.Subset.trans self_subset_closure self_subset_closure)

theorem closure_exchange_property
  (hx : x ∉ s) (hy : y ∉ s) (hs : s ∪ {x} ∈ₛ G)
  (h : x ∈ G.closure (s ∪ {y})) :
    y ∈ G.closure (s ∪ {x}) := sorry

/-- `cospanning` is an equivalence relation in `2^E`. -/
def cospanning (G : Greedoid α) (s t : Finset α) := G.closure s = G.closure t

section cospanning

theorem cospanning_refl : ∀ s, G.cospanning s s := by simp [cospanning]

theorem cospanning_symm (h : G.cospanning s t) : G.cospanning t s := by
  simp only [cospanning] at h; simp only [cospanning, h]

theorem cospanning_comm : G.cospanning s t ↔ G.cospanning t s :=
  ⟨cospanning_symm, cospanning_symm⟩

theorem cospanning_trans {s t u : Finset α}
  (hst : G.cospanning s t) (htu : G.cospanning t u) :
    G.cospanning s u := by
  simp only [cospanning] at hst htu; simp only [cospanning, hst, htu]

theorem cospanning_eqv : Equivalence (G.cospanning) :=
  ⟨cospanning_refl, cospanning_symm, cospanning_trans⟩

theorem cospanning_rel_left_union (h : G.cospanning s t) : G.cospanning s (s ∪ t) := sorry

theorem cospanning_rel_right_union (h : G.cospanning s t) : G.cospanning (s ∪ t) t :=
  cospanning_trans (cospanning_symm (cospanning_rel_left_union h)) h

theorem cospanning_rel_between_subset_left {s t u : Finset α}
  (hst : s ⊆ t) (htu : t ⊆ u) (hsu : G.cospanning s u) :
    G.cospanning s t := sorry

theorem cospanning_rel_between_subset_right {s t u : Finset α}
  (hst : s ⊆ t) (htu : t ⊆ u) (hsu : G.cospanning s u) :
    G.cospanning t u :=
  G.cospanning_trans (cospanning_symm (cospanning_rel_between_subset_left hst htu hsu)) hsu

theorem cospanning_rel_ex
  (h₁ : G.cospanning (s ∪ {y}) (s ∪ {x, y}))
  (h₂ : ¬ G.cospanning (s ∪ {x}) (s ∪ {x, y})) :
    ∃ z ∈ s ∪ {x}, G.cospanning ((s ∪ {x}) \ {z}) (s ∪ {x}) := sorry

theorem cospanning_rel_ex'
  (h₁ : G.cospanning (s ∪ {y}) (s ∪ {x, y}))
  (h₂ : ¬ G.cospanning (s ∪ {x}) (s ∪ {x, y})) :
    ∃ z ∈ s ∪ {x}, G.cospanning (s ∪ {x}) ((s ∪ {x}) \ {z}) :=
  let ⟨z, hz⟩ := cospanning_rel_ex h₁ h₂
  ⟨z, hz.1, G.cospanning_symm hz.2⟩

end cospanning

end closure

end Greedoid

-- TODO: Move to Matroid.Basic.lean

/-- A Matroid. -/
structure Matroid (α : Type _) [Fintype α] [DecidableEq α] extends Greedoid α where
  /-- Matroid is a greedoid without lower bound. -/
  wo_lower_bound :
    {A : Finset α} → A ∈ system.feasible_set →
    {B : Finset α} → B ∈ system.feasible_set → A ⊆ B →
    {x : α} → x ∉ B →
    B ∪ {x} ∈ system.feasible_set →
    A ∪ {x} ∈ system.feasible_set

namespace Matroid

variable {α : Type _} [Fintype α] [DecidableEq α]

theorem has_no_lower_bound {M : Matroid α} : M.interval_property_wo_lower_bound := M.wo_lower_bound

/-- `s ∈ₛ M` if `s` is feasible. -/
def finsetMem (s : Finset α) (M : Matroid α) := s ∈ M.system.feasible_set

/-- `w ∈ₗ M` if `w` is in the language. -/
def wordMem (w : List α) (M : Matroid α) := w ∈ M.language.language

@[inherit_doc] infix:50 " ∈ₛ " => Matroid.finsetMem
/-- Negated version of `∉ₛ` -/
infix:50 " ∉ₛ " => fun s G => ¬ (Matroid.finsetMem s G)
@[inherit_doc] infix:50 " ∈ₗ " => Matroid.wordMem
/-- Negated version of `∉ₗ` -/
infix:50 " ∉ₗ " => fun w G => ¬ (Matroid.wordMem w G)
/-- Prefer `∈` For matroids. -/
instance : Membership (Finset α) (Matroid α) where
  mem s M := s ∈ M.system.feasible_set

@[simp]
theorem system_feasible_set_mem_mem {M : Matroid α} {s : Finset α} :
    s ∈ M.system.feasible_set ↔ s ∈ M := by rfl

section IndependentSet

variable {M : Matroid α} (Sys : Finset (Finset α))

/-- The first independent axiom for matroid. -/
def I₁ := ∅ ∈ Sys

/-- The second independent axiom for matroid. -/
def I₂ := {s : Finset α} → s ∈ Sys → {t : Finset α} → t ⊆ s → t ∈ Sys

/-- The third independent axiom for matroid. -/
def I₃ := {s : Finset α} → s ∈ Sys → {t : Finset α} → t ∈ Sys →
  t.card < s.card → ∃ x ∈ s \ t, t ∪ {x} ∈ Sys

/-- A list of independence axioms for matroid. -/
def matroidIndependenceAxiom := I₁ Sys ∧ I₂ Sys ∧ I₃ Sys

theorem matroid_I₁ : I₁ M.system.feasible_set := by simp only [I₁, M.system.contains_empty]

theorem matroid_I₂ : I₂ M.system.feasible_set := by
  intro s hs t ht
  by_contra' h
  wlog hMinimal : ∀ t', t' ⊆ s → t' ∉ M → t.card ≤ t'.card generalizing s t
  . simp_all
    sorry
  . have t_nonempty : t.Nonempty := by
      apply Finset.nonempty_of_ne_empty; intro h'; apply h; rw [h']; exact M.system.contains_empty
    let ⟨x, hx⟩ := t_nonempty
    sorry

theorem matroid_I₃ : I₃ M.system.feasible_set := by
  intro s hs t ht h
  simp_all
  let ⟨a, ha₁, ha₂⟩ := M.system.exchangeAxiom hs ht h
  simp at ha₁
  exists a

theorem matroid_matroidIndependenceAxiom {M : Matroid α} :
  matroidIndependenceAxiom M.system.feasible_set := ⟨matroid_I₁, matroid_I₂, matroid_I₃⟩

/-- A set system satisfying `matroidIndependenceAxiom` generates a unique matroid. -/
def ofSetSystem (Sys : Finset (Finset α)) (hSys : matroidIndependenceAxiom Sys) :
    Matroid α :=
  let Sys' : GreedoidSystem α := ⟨Sys, hSys.1, fun {s₁} hs₁ {s₂} hs₂ hs => hSys.2.2 hs₁ hs₂ hs⟩
  ⟨⟨Sys'.fromSystemToLanguage, Sys', by rw [fromSystemToLanguage_fromLanguageToSystem_eq], rfl⟩,
    fun {s₁} hs₁ {s₂} hs₂ hs {x} hx₁ hx₂ => by
      simp_all
      let ⟨i₁, i₂, i₃⟩ := hSys
      simp [I₃] at i₃
      let ⟨y, ⟨hy₁, hy₂⟩, hy₃⟩ := @i₃ (s₂ ∪ {x}) hx₂ s₁ hs₁
        (by simp_arith [hx₁, Finset.card_le_of_subset hs])
      by_cases x = y
      . rw [h]; exact hy₃
      . simp at hy₁
        apply hy₁.elim <;> intro h' <;> simp_all
        simp [I₂] at i₂
        apply i₂ hx₂
        intro z hz; simp; simp at hz
        tauto⟩
end IndependentSet

end Matroid

-- TODO: Move to Matroid.LinearMatroid.lean

/-- Linear Matroid is a Matroid which has ground set of column vectors
    of some matrix over some field. -/
structure LinearMatroid (α : Type _) [Fintype α] [DecidableEq α] extends Matroid α where

namespace LinearMatroid

variable {α : Type _} [Fintype α] [DecidableEq α]

def ofMatrix {β F} [Fintype β] [Field F] [DecidableEq F] (A : Matrix β α F) : Matroid α :=
  let col : α → (β → F) := fun a => (fun b => A b a)
  Matroid.ofSetSystem
    (@Finset.filter _
      (fun s => LinearIndependent (β → F) (fun a : {x // x ∈ s} => col a))
      (fun s => sorry) Finset.univ.powerset) (by
    simp [Matroid.matroidIndependenceAxiom, Matroid.I₁, Matroid.I₂, Matroid.I₃]
    constructor <;> try constructor
    . sorry
    . sorry
    . sorry)

end LinearMatroid

-- TODO: Move to Antimatroid.Basic.lean

/-- The Antimatroid. -/
structure Antimatroid (α : Type _) [Fintype α] [DecidableEq α] extends Greedoid α where
  /-- Antimatroids are greedoids without upper bound. -/
  wo_upper_bound :
    {A : Finset α} → A ∈ system.feasible_set →
    {B : Finset α} → B ∈ system.feasible_set → B ⊆ A →
    {x : α} → x ∉ A →
    B ∪ {x} ∈ system.feasible_set → A ∪ {x} ∈ system.feasible_set

namespace Antimatroid

variable {α : Type _} [Fintype α] [DecidableEq α] {A : Antimatroid α}

theorem has_no_upper_bound : A.interval_property_wo_upper_bound := A.wo_upper_bound

theorem is_full : A.full := sorry

end Antimatroid
