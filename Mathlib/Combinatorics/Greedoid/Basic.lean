import Mathlib.Data.List.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.List
import Mathlib.Tactic.TFAE

/-  Note: We distinguish `w` as a `Word` from `l` as a `List`, but use the same type
    as there are so many functionalities given with `List`. -/

/-- The exchange axiom for set systems -/
def exchange_axiom {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) :=
  {s₁ : Finset α} → (hs₁ : s₁ ∈ Sys) →
  {s₂ : Finset α} → (hs₂ : s₂ ∈ Sys) →
  (hs : s₁.card > s₂.card) →
    ∃ x ∈ s₁ \ s₂, s₂ ∪ {x} ∈ Sys

/-- Accessible sets are defined as an associated set system of hereditary language;
    here we only pick its properties. -/
def accessible {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) :=
  ∅ ∈ Sys ∧ (∀ s ∈ Sys, s ≠ ∅ → ∃ x : α, s \ {x} ∈ Sys)

protected theorem Finset.card_induction_on {α : Type _} {p : Finset α → Prop} [DecidableEq α]
  (s : Finset α) (empty : p ∅)
    (insert : ∀ {s : Finset α},
      (∃ t : Finset α, t.card + 1 = s.card ∧ t ⊆ s ∧ p t) → p s) : p s := by
  induction' s using Finset.induction_on with a s ha ih
  . exact empty
  . exact insert ⟨s, by simp [ha], fun x hx => by simp; exact Or.inr hx, ih⟩

namespace SetSystem

variable {α : Type _} [Fintype α] [DecidableEq α]

/-- Base of a set system is the collection of feasible sets which is maximal. -/
def base (Sys : Finset (Finset α)) : Finset (Finset α) :=
  Sys.filter (fun s => ∀ a, a ∉ s → s ∪ {a} ∉ Sys)

/-- Bases of a set `a` given a set system is
    the collection of feasible sets which is maximal in `a`. -/
def bases (Sys : Finset (Finset α)) (s : Finset α) : Finset (Finset α) :=
  Sys.filter (fun s' => s' ⊆ s ∧ (∀ a, a ∉ s' → a ∉ s ∨ s' ∪ {a} ∉ Sys))

theorem base_bases_eq {Sys : Finset (Finset α)} :
    base Sys = bases Sys (@Finset.univ α _) := by ext s; simp [bases, base]

end SetSystem

section ExchangeAxioms

open List Finset

variable {α : Type _} [Fintype α] [DecidableEq α]

/-- A weak version of exchange axiom of set system version of greedoid -/
def weak_exchange_axiom (Sys : Finset (Finset α)) :=
  {s₁ : Finset α} → (hs₁ : s₁ ∈ Sys) →
  {s₂ : Finset α} → (hs₂ : s₂ ∈ Sys) →
  (hs : s₁.card = s₂.card + 1) →
    ∃ x ∈ s₁ \ s₂, s₂ ∪ {x} ∈ Sys

/-- A weaker version of exchange axiom of set system version of greedoid -/
def weaker_exchange_axiom (Sys : Finset (Finset α)) :=
  {s : Finset α} →
  {x : α} → (hx₁ : x ∉ s) → (hx₂ : s ∪ {x} ∈ Sys) →
  {y : α} → (hy₁ : y ∉ s) → (hy₂ : s ∪ {y} ∈ Sys) →
  {z : α} → (hz : z ∉ s) →
  (hxz : s ∪ {x, z} ∈ Sys) → (hxy : s ∪ {x, y} ∉ Sys) →
    s ∪ {y, z} ∈ Sys

theorem exchange_axioms_TFAE {Sys : Finset (Finset α)} (hSys : accessible Sys) :
    TFAE [exchange_axiom Sys, weak_exchange_axiom Sys, weaker_exchange_axiom Sys] := by
  tfae_have 1 → 2
  {
    intro h _ hs₁ _ hs₂ hs
    let ⟨x, hx⟩ := h hs₁ hs₂ (by simp [hs])
    exact ⟨x, hx⟩
  }
  tfae_have 2 → 1
  { sorry }
  tfae_have 2 → 3
  {
    intro h s x hx₁ hx₂ y hy₁ hy₂ z hz hxz hxy
    let ⟨z', hz₁', hz₂'⟩ := h hxz hy₂ (by admit)
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
  tfae_have 3 → 2
  { sorry }
  tfae_finish

theorem exchange_property_bases_card_iff {Sys : Finset (Finset α)} :
    exchange_axiom Sys ↔ (∀ a : Finset α,
      ∀ b₁ ∈ SetSystem.bases Sys a, ∀ b₂ ∈ SetSystem.bases Sys a,
      b₁.card = b₂.card) := by
  simp [exchange_axiom, SetSystem.bases]
  constructor <;> intro h
  . intro a b₁ hb₁₁ hb₁₂ hb₁₃ b₂ hb₂₁ hb₂₂ hb₂₃
    by_contra' h'
    by_cases h'' : (b₁.card < b₂.card)
    . let ⟨x, ⟨hx₁, hx₂⟩, hx₃⟩ := h hb₂₁ hb₁₁ h''
      apply (hb₁₃ x hx₂).elim <;> intro h'''
      . exact h''' (hb₂₂ hx₁)
      . exact h''' hx₃
    . have h'' : b₂.card < b₁.card := by
        apply (Nat.eq_or_lt_of_not_lt h'').elim <;> intro <;> try trivial
      let ⟨x, ⟨hx₁, hx₂⟩, hx₃⟩ := h hb₁₁ hb₂₁ h''
      apply (hb₂₃ x hx₂).elim <;> intro h'''
      . exact h''' (hb₁₂ hx₁)
      . exact h''' hx₃
  . intro s₁ hs₁ s₂ hs₂ hs
    by_contra' h'
    have := h (s₁ ∪ s₂) s₂ hs₂ (fun x hx => by simp [hx]) (fun a ha => by
      by_cases (a ∈ s₁ ∪ s₂)
      . simp [ha] at h
        exact Or.inr (h' _ ⟨h, ha⟩)
      . exact Or.inl h)
    sorry

end ExchangeAxioms

/-- Language version of greedoid. -/
structure GreedoidLanguage (α : Type _) [Fintype α] where
  /-- `language` is a finite sequence of words. -/
  language : Finset (List α)
  /-- Every words of the `language` are simple, i.e., no words contains duplicates. -/
  simple : ∀ w ∈ language, w.Nodup
  /-- `language` contains an empty word. -/
  contains_empty : [] ∈ language
  /-- For every word `w = w₂ ++ w₁ ∈ language`, `w₁ ∈ language` also holds. -/
  contains_prefix : ∀ w₁ w₂ : List α, w₂ ++ w₁ ∈ language → w₁ ∈ language
  /-- Exchange Axiom -/
  exchange_axiom : {w₁ : List α} → w₁ ∈ language → {w₂ : List α} → w₂ ∈ language →
    w₁.length > w₂.length → ∃ x ∈ w₁, x :: w₂ ∈ language

/-- List of axioms in `GreedoidLanguage` -/
def greedoidLanguageAxiom {α : Type _} (Lang : Finset (List α)) :=
  (∀ w ∈ Lang, w.Nodup) ∧
  (∅ ∈ Lang) ∧
  (∀ w₁ w₂ : List α, w₂ ++ w₁ ∈ Lang → w₁ ∈ Lang) ∧
  ({w₁ : List α} → w₁ ∈ Lang → {w₂ : List α} → w₂ ∈ Lang →
    w₁.length > w₂.length → ∃ x ∈ w₁, x :: w₂ ∈ Lang)

theorem greedoidLanguageAxiom_greedoidLangauge {α : Type _} [Fintype α] {L : GreedoidLanguage α} :
    greedoidLanguageAxiom L.language :=
  ⟨L.simple, L.contains_empty, L.contains_prefix, L.exchange_axiom⟩

/-- Set System version of greedoid. -/
structure GreedoidSystem (α : Type _) [Fintype α] [DecidableEq α] where
  /-- `feasible_set` contains sets which are feasible. -/
  feasible_set : Finset (Finset α)
  /-- `feasible_set` contains an empty set. -/
  contains_empty : ∅ ∈ feasible_set
  /-- Exchange Axiom -/
  exchange_axiom : exchange_axiom feasible_set

/-- List of axioms in `GreedoidSystem` -/
def greedoidSystemAxiom {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) :=
  ∅ ∈ Sys ∧ exchange_axiom Sys

theorem greedoidSystemAxiom_greedoidSystem {α : Type _} [Fintype α] [DecidableEq α]
  {S : GreedoidSystem α} :
    greedoidSystemAxiom S.feasible_set :=
  ⟨S.contains_empty, S.exchange_axiom⟩

/-- Checks if the converted set equals the feasible set.

    `feasible_set = {↑w | w ∈ language}` -/
protected def GreedoidLanguage.fromLanguageToSystem {α : Type _} [Fintype α] [DecidableEq α]
  (L : GreedoidLanguage α) := L.language.image (fun w : List α => (w.toFinset : Finset α))

theorem greedoidSystemAxiom_fromLanguageToSystem {α : Type _} [Fintype α] [DecidableEq α]
  {L : GreedoidLanguage α} :
    greedoidSystemAxiom L.fromLanguageToSystem := ⟨by
  simp [GreedoidLanguage.fromLanguageToSystem, L.contains_empty], by
  simp [GreedoidLanguage.fromLanguageToSystem, exchange_axiom]
  intro w₁ hw₁ w₂ hw₂ hw
  have := L.exchange_axiom hw₁ hw₂
  rw [List.toFinset_card_of_nodup (L.simple _ hw₁),
    List.toFinset_card_of_nodup (L.simple _ hw₂)] at hw
  let ⟨s, hs⟩ := this hw
  exists s
  apply And.intro
  . apply And.intro hs.1
    have := L.simple _ hs.2
    simp at this; exact this.1
  . exists s :: w₂
    apply And.intro hs.2
    ext x
    constructor <;> intro h
    . simp at h
      apply h.elim <;> intro h <;> simp [h]
    . simp at h
      apply h.elim <;> intro h <;> simp [h]⟩

/-- Checks if the converted language equals the language.

    `language = {w | underlying set of every prefix of w is feasible}` -/
protected def GreedoidSystem.fromSystemToLanguage {α : Type _} [Fintype α] [DecidableEq α]
  (S : GreedoidSystem α) : Finset (List α) :=
  let perm_set := Finset.bunionᵢ (S.feasible_set.map ⟨fun s => s.val.lists, by
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
  (perm_set.filter (fun l => ∀ l' ∈ l.tails, l'.toFinset ∈ S.feasible_set))

theorem greedoidLanguageAxiom_fromSystemToLanguage {α : Type _} [Fintype α] [DecidableEq α]
  {S : GreedoidSystem α} :
    greedoidLanguageAxiom S.fromSystemToLanguage := sorry

/-- `relatedLanguageSystem` checks if a given language and system are related to each other.
    That is, given that the language is hereditary,

    1. `feasible_set = {↑w | w ∈ language}`
    2. `language = {w | underlying set of every prefix of w is feasible}` -/
protected def Greedoid.relatedLanguageSystem {α : Type _} [Fintype α] [DecidableEq α]
  (L : GreedoidLanguage α) (S : GreedoidSystem α) : Prop :=
  S.feasible_set = L.fromLanguageToSystem ∧ L.language = S.fromSystemToLanguage

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
/-- Prefer `∈ₛ` For greedoids. -/
instance {α : Type _} [Fintype α] [DecidableEq α] :
  Membership (Finset α) (Greedoid α) := ⟨Greedoid.finsetMem⟩

namespace Greedoid

open List Finset Multiset

variable {α : Type _} [Fintype α] [DecidableEq α] {G : Greedoid α}

section Membership

theorem emptyset_finsetMem : (∅ : Finset α) ∈ₛ G := G.system.contains_empty

theorem nil_wordMem : ([] : List α) ∈ₗ G := G.language.contains_empty

theorem emptyset_mem : (∅ : Finset α) ∈ G := G.system.contains_empty

theorem nil_toFinset_mem : [].toFinset ∈ G := G.system.contains_empty

theorem wordMem_nodup {w : List α} (hw : w ∈ₗ G) : w.Nodup := G.language.simple _ hw

@[simp]
theorem finsetMem_mem_iff {s : Finset α} :
    s ∈ G ↔ s ∈ₛ G := by rfl

theorem word_mem_language_toFinset_mem {w : List α} (hw : w ∈ₗ G) :
    w.toFinset ∈ₛ G := by
  have := G.related.1
  simp [Greedoid.finsetMem, this, GreedoidLanguage.fromLanguageToSystem]
  exists w

theorem finset_feasible_exists_word {s : Finset α} (hs : s ∈ₛ G) :
    ∃ w : List α, w ∈ₗ G ∧ s = w.toFinset := by
  simp [Greedoid.finsetMem, G.related.1, GreedoidLanguage.fromLanguageToSystem] at hs
  let ⟨a, ha₁, ha₂⟩ := hs
  exists a; exact And.intro ha₁ ha₂.symm

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
        simp [this, GreedoidLanguage.fromLanguageToSystem, Greedoid.finsetMem]
        simp [G.related.1, GreedoidLanguage.fromLanguageToSystem]
        exists t

end Membership

theorem greedoid_system_accessible : accessible G.system.feasible_set := by
  simp [accessible, G.system.contains_empty]
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
      rw [Finset.sdiff_singleton_not_mem_eq_self]
      . rw [G.related.1]
        simp [GreedoidLanguage.fromLanguageToSystem]
        exists t
      . simp [this.1]

theorem weak_exchange_axiom' : weak_exchange_axiom G.system.feasible_set := by
  apply ((exchange_axioms_TFAE greedoid_system_accessible).out 0 1).mp
  exact G.system.exchange_axiom

theorem weaker_exchange_axiom' : weaker_exchange_axiom G.system.feasible_set := by
  apply ((exchange_axioms_TFAE greedoid_system_accessible).out 0 2).mp
  exact G.system.exchange_axiom

/-- Greedoid is full if the ground set is feasible. -/
def full (G : Greedoid α) := (@Finset.univ α _) ∈ₛ G

/-- The interval property is satisfied by matroids, antimatroids, and some greedoids. -/
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

theorem bases_nonempty {s : Finset α} : Nonempty (G.bases s) := by
  sorry

theorem bases_card_eq {s : Finset α}
  {b₁ : Finset α} (hb₁ : b₁ ∈ G.bases s)
  {b₂ : Finset α} (hb₂ : b₂ ∈ G.bases s) :
    b₁.card = b₂.card := by
  by_contra'
  rw [← lt_or_lt_iff_ne] at this
  apply this.elim <;> intro h <;> clear hb₂ <;> clear this
  . sorry
  . sorry

theorem basis_of_full_unique (hG : G.full) : ∃! b, b ∈ G.base := by
  exists univ
  sorry

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

@[simp]
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

theorem rank_eq_card_iff_feasible : G.rank s = s.card ↔ s ∈ₛ G := by
  constructor <;> intro h
  . sorry
  . exact rank_of_feasible h

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
    sorry
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

structure Matroid (α : Type _) [Fintype α] [DecidableEq α] extends Greedoid α where
  wo_lower_bound :
    {A : Finset α} → A ∈ system.feasible_set →
    {B : Finset α} → B ∈ system.feasible_set → A ⊆ B →
    {x : α} → x ∉ B →
    B ∪ {x} ∈ system.feasible_set → A ∪ {x} ∈ system.feasible_set

namespace Matroid

variable {α : Type _} [Fintype α] [DecidableEq α]

theorem has_no_lower_bound {M : Matroid α} : M.interval_property_wo_lower_bound := M.wo_lower_bound

/-- `s ∈ₛ M` if `s` is feasible. -/
def Matroid.finsetMem (s : Finset α) (M : Matroid α) := s ∈ M.system.feasible_set

/-- `w ∈ₗ M` if `w` is in the language. -/
def Matroid.wordMem (w : List α) (M : Matroid α) := w ∈ M.language.language

@[inherit_doc] infix:50 " ∈ₛ " => Matroid.finsetMem
/-- Negated version of `∉ₛ` -/
infix:50 " ∉ₛ " => fun s G => ¬ (Matroid.finsetMem s G)
@[inherit_doc] infix:50 " ∈ₗ " => Matroid.wordMem
/-- Negated version of `∉ₗ` -/
infix:50 " ∉ₗ " => fun w G => ¬ (Matroid.wordMem w G)
/-- Prefer `∈` For matroids. -/
instance : Membership (Finset α) (Matroid α) where
  mem s M := s ∈ M.system.feasible_set

section IndependentSet

variable {M : Matroid α} (Sys : Finset (Finset α))

def I₁ := ∅ ∈ Sys

def I₂ := {s : Finset α} → s ∈ Sys → {t : Finset α} → t ⊆ s → t ∈ Sys

def I₃ := {s : Finset α} → s ∈ Sys → {t : Finset α} → t ∈ Sys →
  s.card = t.card + 1 → ∃ x ∈ s \ t, t ∪ {x} ∈ Sys

def matroidIndependenceAxiom := I₁ Sys ∧ I₂ Sys ∧ I₃ Sys

theorem matroid_I₁ : I₁ M.system.feasible_set := by simp [I₁, M.system.contains_empty]

theorem matroid_I₂ : I₂ M.system.feasible_set := sorry

theorem matroid_I₃ : I₃ M.system.feasible_set := sorry



end IndependentSet

end Matroid

-- TODO: Move to Antimatroid.Basic.lean

structure Antimatroid (α : Type _) [Fintype α] [DecidableEq α] extends Greedoid α where
  wo_upper_bound :
    {A : Finset α} → A ∈ system.feasible_set →
    {B : Finset α} → B ∈ system.feasible_set → B ⊆ A →
    {x : α} → x ∉ A →
    B ∪ {x} ∈ system.feasible_set → A ∪ {x} ∈ system.feasible_set

namespace Antimatroid

variable {α : Type _} [Fintype α] [DecidableEq α] {A : Antimatroid α}

theorem has_no_upper_bound : A.interval_property_wo_upper_bound := A.wo_upper_bound



end Antimatroid
