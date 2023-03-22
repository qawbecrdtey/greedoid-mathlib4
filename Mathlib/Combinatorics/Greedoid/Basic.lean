import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-- A `Word` is an alternative of `List` which gets finite type as an input.
    Always keep in mind that unlike `List`, left is back and right is front.
    For example, `w₁` is a prefix of `w₂ ++ w₁`, and w₂ is a postfix. -/
def Word (α : Type _) [Fintype α] := List α

section Word

variable {α : Type _} [Fintype α]

/-- Length of a word. -/
protected def Word.length (w : Word α) := List.length w

/-- `w` contains no duplicates. -/
protected def Word.simple (w : Word α) := w.Nodup

/-- Conversion from `Word α` to `Finset α`. -/
protected def Word.toFinset [DecidableEq α] (w : Word α) := List.toFinset w

instance : HAppend (Word α) (Word α) (Word α) := ⟨List.append⟩

instance : SizeOf (Word α) := ⟨List.length⟩

instance : Coe (Word α) (List α) := ⟨id⟩

instance [DecidableEq α] : Coe (Word α) (Finset α) := ⟨fun w => w.toFinset⟩

instance : Membership α (Word α) := ⟨List.Mem⟩

instance : EmptyCollection (Word α) := ⟨[]⟩

instance : Inhabited (Word α) := ⟨∅⟩

end Word

/-- Language version of greedoid. -/
structure GreedoidLanguage (α : Type _) [Fintype α] where
  /-- `language` is a finite sequence of words. -/
  language : Finset (Word α)
  /-- Every words of the `language` are simple, i.e., no words contains duplicates. -/
  simple : ∀ w ∈ language, w.simple
  /-- `language` contains an empty word. -/
  contains_empty : ∅ ∈ language
  /-- For every word `w = w₂ ++ w₁ ∈ language`, `w₁ ∈ language` also holds. -/
  contains_prefix : ∀ w₁ w₂ : Word α, w₂ ++ w₁ ∈ language → w₁ ∈ language
  /-- Exchange Axiom -/
  exchange_axiom : {w₁ : Word α} → w₁ ∈ language → {w₂ : Word α} → w₂ ∈ language →
    w₁.length > w₂.length → ∃ x ∈ w₁, x :: w₂ ∈ language

/-- Set System version of greedoid. -/
structure GreedoidSystem (α : Type _) [Fintype α] [DecidableEq α] where
  /-- `feasible_set` contains sets which are feasible. -/
  feasible_set : Finset (Finset α)
  /-- `feasible_set` contains an empty set. -/
  contains_empty : ∅ ∈ feasible_set
  /-- Exchange Axiom -/
  exchange_axiom : {s₁ : Finset α} → s₁ ∈ feasible_set → {s₂ : Finset α} → s₂ ∈ feasible_set →
    s₁.card > s₂.card → ∃ x ∈ s₁ \ s₂, s₂ ∪ {x} ∈ feasible_set

/-- `relatedLanguageSystem` checks if a given language and system are related to each other.
    That is, given that the language is hereditary,

    1. `feasible_set = {↑w | w ∈ language}`
    2. `language = {w | underlying set of every prefix of w is feasible}` -/
protected def Greedoid.relatedLanguageSystem {α : Type _} [Fintype α] [DecidableEq α]
  (L : GreedoidLanguage α) (S : GreedoidSystem α) : Prop :=
  S.feasible_set = L.language.image (fun w : Word α => (↑w : Finset α)) ∧
  sorry -- `language = {w | underlying set of every prefix of w is feasible}`

/-- Merging of language and system version of greedoid.
    This will (potentially) help `Greedoid` cover theorems written in
    both language and systems. -/
structure Greedoid (α : Type _) [Fintype α] [DecidableEq α] where
  /-- Greedoid as a language. -/
  greedoid_language : GreedoidLanguage α
  /-- Greedoid as a system. -/
  greedoid_system : GreedoidSystem α
  /-- `greedoid_language` and `greedoid_system` are related. -/
  related : Greedoid.relatedLanguageSystem greedoid_language greedoid_system
