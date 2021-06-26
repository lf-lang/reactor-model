import order.lexicographic
import data.finset

open_locale classical

-- The type of opaque values that underlie TPAs.
-- Their equality has to be decidable, but beyond that their values are of no interest.
variables (υ : Type*) [decidable_eq υ]

-- A tag is a logical timestamp.
-- The first component is the time value, the second component is the microstep index.
-- Their ordering is lexicographical.
@[derive linear_order]
def tag := lex ℕ ℕ  

-- A TPA is a finite set of tag-value pairs where each tag is unique. 
-- They are the primitive values used in timed reactor networks.
-- Since instantaneous networks wrap their primitive values in `option`, 
-- we require TPAs to be non-empty in order to avoid distinct representations
-- of the absent value (`∅` and `none`).
structure tpa := 
  (pairs : finset (tag × υ))
  (unique: ∀ p p' ∈ pairs, prod.fst p = prod.fst p' → p = p')
  (nonempty : pairs.nonempty)

variable {υ}

namespace tpa

  -- A constructor for a TPA that can handle an optional *value*.
-- If the given value is `none`, instead of returning an empty TPA
-- (which isn't possible) by the definition of TPAs, we return `none`.
-- Otherwise we construct a TPA with exactly one tag-value pair.
def maybe : tag → option υ → option (tpa υ)
  | _ none := none
  | t (some v) := some { tpa .
    pairs := {(t, v)},
    unique := by { intros p p', simp, intros h h' _, rw [h, h'] },
    nonempty := by simp
  } 

-- A TPA's "map" is a functional representation of its tag-value pairs,
-- as a map from tags to sets of values. As TPAs can't actually have more
-- than one value per tag (by their `unique` property), this is just a
-- preliminary definition, used for `tpa.map`.
def map' (p : tpa υ) : tag → set υ := λ t, { v | (t, v) ∈ p.pairs }

-- A TPA's map can never assign more than one value to each tag, i.e. the
-- returned sets are all subsingletons.
lemma map_subsingleton (tp : tpa υ) (t : tag) : (tp.map' t).subsingleton :=
  begin
    unfold set.subsingleton tpa.map',
    intros x hₓ x' hₓ',
    rw set.mem_set_of_eq at hₓ hₓ',
    have h, from tp.unique _ _ hₓ hₓ',
    replace h := h (refl _),
    injection h
  end

-- A TPA's "map" is a functional representation of its tag-value pairs,
-- as a map from tags to values. For a given tag the assigned value is `none`,
-- if the TPA does not contain a tag-value pair for that tag.
noncomputable def map (p : tpa υ) : tag → option υ := λ t, 
  (p.map_subsingleton t)
    .eq_empty_or_singleton
    .by_cases (λ _, none) (λ s, s.some)

end tpa