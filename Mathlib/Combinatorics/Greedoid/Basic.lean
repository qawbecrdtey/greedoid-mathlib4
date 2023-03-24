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
  contains_empty : ∅ ∈ language
  /-- For every word `w = w₂ ++ w₁ ∈ language`, `w₁ ∈ language` also holds. -/
  contains_prefix : ∀ w₁ w₂ : List α, w₂ ++ w₁ ∈ language → w₁ ∈ language
  /-- Exchange Axiom -/
  exchange_axiom : {w₁ : List α} → w₁ ∈ language → {w₂ : List α} → w₂ ∈ language →
    w₁.length > w₂.length → ∃ x ∈ w₁, x :: w₂ ∈ language

/-- Set System version of greedoid. -/
structure GreedoidSystem (α : Type _) [Fintype α] [DecidableEq α] where
  /-- `feasible_set` contains sets which are feasible. -/
  feasible_set : Finset (Finset α)
  /-- `feasible_set` contains an empty set. -/
  contains_empty : ∅ ∈ feasible_set
  /-- Exchange Axiom -/
  exchange_axiom : exchange_axiom feasible_set

/-- Checks if the converted set equals the feasible set.

    `feasible_set = {↑w | w ∈ language}` -/
protected def Greedoid.fromLanguageToSystem {α : Type _} [Fintype α] [DecidableEq α]
  (L : GreedoidLanguage α) := L.language.image (fun w : List α => (w.toFinset : Finset α))

/-- Checks if the converted language equals the language.

    `language = {w | underlying set of every prefix of w is feasible}` -/
protected def Greedoid.fromSystemToLanguage {α : Type _} [Fintype α] [DecidableEq α]
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

/-- `relatedLanguageSystem` checks if a given language and system are related to each other.
    That is, given that the language is hereditary,

    1. `feasible_set = {↑w | w ∈ language}`
    2. `language = {w | underlying set of every prefix of w is feasible}` -/
protected def Greedoid.relatedLanguageSystem {α : Type _} [Fintype α] [DecidableEq α]
  (L : GreedoidLanguage α) (S : GreedoidSystem α) : Prop :=
  S.feasible_set = Greedoid.fromLanguageToSystem L ∧ L.language = Greedoid.fromSystemToLanguage S

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
protected def Greedoid.listMem {α : Type _} [Fintype α] [DecidableEq α]
  (w : List α) (G : Greedoid α) := w ∈ G.language.language

@[inherit_doc] infix:50 " ∈ₛ " => Greedoid.finsetMem
/-- Negated version of `∉ₛ` -/
infix:50 " ∉ₛ " => fun s G => ¬ (Greedoid.finsetMem s G)
@[inherit_doc] infix:50 " ∈ₗ " => Greedoid.listMem
/-- Negated version of `∉ₗ` -/
infix:50 " ∉ₗ " => fun w G => ¬ (Greedoid.listMem w G)
instance {α : Type _} [Fintype α] [DecidableEq α] :
  Membership (Finset α) (Greedoid α) := ⟨Greedoid.finsetMem⟩

namespace Greedoid

open List Finset Multiset

variable {α : Type _} [Fintype α] [DecidableEq α]

theorem greedoid_system_accessible {G : Greedoid α} : accessible G.system.feasible_set := by
  simp [accessible, G.system.contains_empty]
  intro s hs₁ hs₂
  induction' s using Finset.induction_on with a s ha ih
  . simp at hs₂
  . sorry

section Membership

theorem emptyset_finsetMem {G : Greedoid α} : (∅ : Finset α) ∈ₛ G := G.system.contains_empty

theorem nil_listMem {G : Greedoid α} : ([] : List α) ∈ₗ G := G.language.contains_empty

theorem emptyset_mem {G : Greedoid α} : (∅ : Finset α) ∈ G := G.system.contains_empty

theorem nil_toFinset_mem {G : Greedoid α} : [].toFinset ∈ G := G.system.contains_empty

theorem finsetMem_mem_iff {G : Greedoid α} {s : Finset α} :
    s ∈ₛ G ↔ s ∈ G := by rfl

theorem word_mem_language_toFinset_mem {G : Greedoid α} {w : List α} (hw : w ∈ₗ G) :
    w.toFinset ∈ G := by
  sorry

theorem finset_feasible_exists_word {G : Greedoid α} {s : Finset α} (hs : s ∈ₛ G) :
    ∃ w : List α, w ∈ₗ G ∧ s = w.toFinset := by
  sorry

theorem finset_feasible_exists_feasible_ssubset {G : Greedoid α} {s : Finset α} (hs : s ≠ ∅) :
    ∃ s', s' ⊂ s ∧ s ∈ₛ G := by
  sorry

end Membership

theorem weak_exchange_axiom' {G : Greedoid α} :
    weak_exchange_axiom G.system.feasible_set := by
  apply ((exchange_axioms_TFAE greedoid_system_accessible).out 0 1).mp
  exact G.system.exchange_axiom

theorem weaker_exchange_axiom' {G : Greedoid α} :
    weaker_exchange_axiom G.system.feasible_set := by
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

end Greedoid
