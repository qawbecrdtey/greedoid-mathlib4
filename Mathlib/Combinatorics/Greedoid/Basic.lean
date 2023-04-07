import Mathlib.Data.List.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Data.List.Infix
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.List
import Mathlib.Tactic.TFAE
import Mathlib.Tactic.WLOG

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
    TFAE [exchangeAxiom Sys, weak_exchange_axiom Sys, weaker_exchange_axiom Sys] := by
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
    exchangeAxiom Sys ↔ (∀ a : Finset α,
      ∀ b₁ ∈ SetSystem.bases Sys a, ∀ b₂ ∈ SetSystem.bases Sys a,
      b₁.card = b₂.card) := by
  simp [exchangeAxiom, SetSystem.bases]
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
    then sorry
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

/-- Set System version of greedoid. -/
structure GreedoidSystem (α : Type _) [Fintype α] [DecidableEq α] where
  /-- `feasible_set` contains sets which are feasible. -/
  feasible_set : Finset (Finset α)
  /-- `feasible_set` contains an empty set. -/
  contains_empty : ∅ ∈ feasible_set
  /-- Exchange Axiom -/
  exchangeAxiom : exchangeAxiom feasible_set

/-- List of axioms in `GreedoidSystem` -/
def greedoidSystemAxiom {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) :=
  ∅ ∈ Sys ∧ exchangeAxiom Sys

instance {α : Type _} [DecidableEq α] :
    DecidablePred (@greedoidSystemAxiom α _) := fun Sys =>
  if h₁ : ∅ ∈ Sys
  then if h₂ : exchangeAxiom Sys
    then isTrue (by simp_all [greedoidSystemAxiom])
    else isFalse (by simp [greedoidSystemAxiom, h₂])
  else isFalse (by simp [greedoidSystemAxiom, h₁])

protected theorem GreedoidSystem.eq_of_veq {α : Type _} [Fintype α] [DecidableEq α] :
    ∀ {S₁ S₂ : GreedoidSystem α}, S₁.feasible_set = S₂.feasible_set → S₁ = S₂
  | ⟨s₁, _, _⟩, ⟨s₂, _, _⟩, h => by cases h; rfl

instance {α : Type _} [Fintype α] [DecidableEq α] :
    DecidableEq (GreedoidSystem α) := fun S₁ S₂ =>
  if h : S₁.feasible_set = S₂.feasible_set
  then isTrue (GreedoidSystem.eq_of_veq h)
  else isFalse (fun h' => h (by simp only [h']))

theorem greedoidSystemAxiom_greedoidSystem {α : Type _} [Fintype α] [DecidableEq α]
  {S : GreedoidSystem α} :
    greedoidSystemAxiom S.feasible_set :=
  ⟨S.contains_empty, S.exchangeAxiom⟩

/-- Checks if the converted set equals the feasible set.

    `feasible_set = {↑w | w ∈ language}` -/
protected def GreedoidLanguage.fromLanguageToSystem' {α : Type _} [Fintype α] [DecidableEq α]
  (L : GreedoidLanguage α) := L.language.image (fun w : List α => (w.toFinset : Finset α))

theorem greedoidSystemAxiom_fromLanguageToSystem' {α : Type _} [Fintype α] [DecidableEq α]
  {L : GreedoidLanguage α} :
    greedoidSystemAxiom L.fromLanguageToSystem' := ⟨by
  simp [GreedoidLanguage.fromLanguageToSystem', L.contains_empty], by
  simp [GreedoidLanguage.fromLanguageToSystem', exchangeAxiom]
  intro w₁ hw₁ w₂ hw₂ hw
  have := L.exchangeAxiom hw₁ hw₂
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

theorem fromLanguageToSystem'_eq {α : Type _} [Fintype α] [DecidableEq α]
  {L₁ L₂ : GreedoidLanguage α} (hL : L₁.fromLanguageToSystem' = L₂.fromLanguageToSystem') :
    L₁ = L₂ := by
  sorry

/-- Converts language to system. -/
protected def GreedoidLanguage.fromLanguageToSystem {α : Type _} [Fintype α] [DecidableEq α]
    (L : GreedoidLanguage α) : GreedoidSystem α :=
  ⟨L.fromLanguageToSystem',
    greedoidSystemAxiom_fromLanguageToSystem'.1,
    greedoidSystemAxiom_fromLanguageToSystem'.2⟩

theorem fromLanguageToSystem_eq {α : Type _} [Fintype α] [DecidableEq α]
  {L₁ L₂ : GreedoidLanguage α} (hL : L₁.fromLanguageToSystem = L₂.fromLanguageToSystem) :
    L₁ = L₂ := by
  apply fromLanguageToSystem'_eq
  simp [GreedoidLanguage.fromLanguageToSystem] at hL
  exact hL

/-- Checks if the converted language equals the language.

    `language = {w | underlying set of every prefix of w is feasible}` -/
protected def GreedoidSystem.fromSystemToLanguage' {α : Type _} [Fintype α] [DecidableEq α]
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

theorem greedoidLanguageAxiom_fromSystemToLanguage' {α : Type _} [Fintype α] [DecidableEq α]
  {S : GreedoidSystem α} :
    greedoidLanguageAxiom S.fromSystemToLanguage' := ⟨fun _ hw => by
  simp [GreedoidSystem.fromSystemToLanguage'] at hw
  let ⟨⟨a, _, ha⟩, _⟩ := hw; clear hw
  rw [← Multiset.coe_nodup]
  exact ha ▸ a.nodup, by
  simp [GreedoidSystem.fromSystemToLanguage', S.contains_empty], fun w₁ w₂ hw => by
  simp [GreedoidSystem.fromSystemToLanguage'] at *
  let ⟨⟨a, _, ha⟩, h⟩ := hw; clear hw
  have : (Multiset.ofList _).Nodup := ha ▸ a.nodup
  simp only [Multiset.coe_nodup] at this
  constructor
  . exists w₁.toFinset
    constructor
    . apply h
      apply Or.inl ⟨[], by simp; exists w₂; simp only [List.append_nil]⟩
    . simp
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
        simp; apply hw.elim <;> tauto, by
  intro w₁ hw₁ w₂ hw₂ hw
  simp [GreedoidSystem.fromSystemToLanguage'] at hw₁ hw₂
  simp [GreedoidSystem.fromSystemToLanguage']
  have w₁_nodup : w₁.Nodup := by
    let ⟨a, _, ha⟩ := hw₁.1; rw [← Multiset.coe_nodup]; exact ha ▸ a.nodup
  have w₂_nodup : w₂.Nodup := by
    let ⟨a, _, ha⟩ := hw₂.1; rw [← Multiset.coe_nodup]; exact ha ▸ a.nodup
  let ⟨x, hx⟩ := @GreedoidSystem.exchangeAxiom α _ _ S w₁.toFinset (hw₁.2 w₁ w₁.suffix_refl)
    w₂.toFinset (hw₂.2 w₂ w₂.suffix_refl) (by
      simp [List.toFinset_card_of_nodup, w₁_nodup, w₂_nodup, hw])
  exists x
  simp at hx; simp [hx]
  have h₁ : insert x w₂.toFinset = w₂.toFinset ∪ {x} := by
    ext a; constructor <;> intro h <;> simp at * <;> tauto
  constructor
  . exists (x :: w₂).toFinset; simp
    simp [hx, List.dedup_eq_self.mpr w₂_nodup, h₁]
    simp [insert, List.insert, hx.1.2]
  . simp [h₁, hx.2]
    exact hw₂.2⟩

theorem fromSystemToLanguage'_eq {α : Type _} [Fintype α] [DecidableEq α]
  {S₁ S₂ : GreedoidSystem α} (hS : S₁.fromSystemToLanguage' = S₂.fromSystemToLanguage') :
    S₁ = S₂ := sorry

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
    {S : GreedoidSystem α} : (S.fromSystemToLanguage).fromLanguageToSystem = S := sorry

@[simp]
theorem fromLanguageToSystem_fromSystemToLanguage_eq {α : Type _} [Fintype α] [DecidableEq α]
    {L : GreedoidLanguage α} : (L.fromLanguageToSystem).fromSystemToLanguage = L := sorry

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

theorem relatedLanguageSystem_eq {α : Type _} [Fintype α] [DecidableEq α]
  {L₁ L₂ : GreedoidLanguage α} {S₁ S₂ : GreedoidSystem α}
  (h₁ : Greedoid.relatedLanguageSystem L₁ S₁)
  (h₂ : Greedoid.relatedLanguageSystem L₂ S₂) :
    L₁ = L₂ ↔ S₁ = S₂ :=
  ⟨fun h => fromSystemToLanguage_eq ((h ▸ h₁.2) ▸ h₂.2),
   fun h => fromLanguageToSystem_eq ((h ▸ h₁.1) ▸ h₂.1)⟩

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

instance : DecidableEq (Greedoid α) := fun G₁ G₂ =>
  if h : G₁.language = G₂.language ∨ G₁.system = G₂.system
  then isTrue (h.elim
    (fun h => eq_of_veq h ((relatedLanguageSystem_eq G₁.related G₂.related).mp h))
    (fun h => eq_of_veq ((relatedLanguageSystem_eq G₁.related G₂.related).mpr h) h))
  else isFalse (fun h' => h (Or.inl (h' ▸ rfl)))

instance : Fintype (Greedoid α) where
  elems := (@Finset.filter (Finset (Finset α)) (fun Sys => greedoidSystemAxiom Sys) sorry
    (@Finset.univ (Finset (Finset α)) _)).image sorry
  complete := sorry

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
    w.toFinset ∈ₛ G := by
  have := G.related.1
  simp [Greedoid.finsetMem, this, GreedoidLanguage.fromLanguageToSystem',
    GreedoidLanguage.fromLanguageToSystem]
  exists w

theorem finset_feasible_exists_word {s : Finset α} (hs : s ∈ₛ G) :
    ∃ w : List α, w ∈ₗ G ∧ s = w.toFinset := by
  simp [Greedoid.finsetMem, G.related.1, GreedoidLanguage.fromLanguageToSystem',
    GreedoidLanguage.fromLanguageToSystem] at hs
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
        simp [this, GreedoidLanguage.fromLanguageToSystem', Greedoid.finsetMem]
        simp [G.related.1, GreedoidLanguage.fromLanguageToSystem',
          GreedoidLanguage.fromLanguageToSystem]
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
        simp [GreedoidLanguage.fromLanguageToSystem', GreedoidLanguage.fromLanguageToSystem]
        exists t
      . simp [this.1]

theorem weak_exchange_axiom' : weak_exchange_axiom G.system.feasible_set := by
  apply ((exchange_axioms_TFAE greedoid_system_accessible).out 0 1).mp
  exact G.system.exchangeAxiom

theorem weaker_exchange_axiom' : weaker_exchange_axiom G.system.feasible_set := by
  apply ((exchange_axioms_TFAE greedoid_system_accessible).out 0 2).mp
  exact G.system.exchangeAxiom

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
protected def Matroid.ofSetSystem (Sys : Finset (Finset α)) (hSys : matroidIndependenceAxiom Sys) :
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



end Antimatroid
