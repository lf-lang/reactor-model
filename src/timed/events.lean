import timed.primitives
import inst.network.ids

open_locale classical

-- The type of opaque values that underlie TPAs.
-- Their equality has to be decidable, but beyond that their values are of no interest.
variables (υ : Type*) [decidable_eq υ]

-- An event map is used as a global structure (on a timed network) to keep track of
-- the events produced by scheduled actions. These events are represented as a map that
-- defines which input port (this will only ever apply to IAPs) should have which value
-- at a given tag. 
def timed.network.event_map := port.id → tag → option υ

namespace timed.network.event_map
open timed.network

  variable {υ}

  -- The tags for which a given event map contains events.
  -- Note that this set also contains all tags from past events.
  def event_tags (μ : event_map υ) : set tag := { t | ∃ p, μ p t ≠ none }

  -- The proposition that a given tag is the next tag for which a given event map
  -- has a scheduled event, starting from a given current tag.
  -- This is the case if the given tag comes after the current tag, but is smaller 
  -- or equal to the tags of all other scheduled events.
  def tag_is_next_after (μ : event_map υ) (n c : tag) : Prop :=
    n ∈ μ.event_tags ∧ (n > c) ∧ (∀ t ∈ μ.event_tags, t > c → n ≤ t)

  -- There can only ever be at most one next tag after a given "current" time, 
  -- for an event map.
  lemma next_tags_subsingleton (μ : event_map υ) (c : tag) :
    { t | μ.tag_is_next_after t c}.subsingleton :=
    begin
      unfold set.subsingleton,
      intros x hx y hy,
      rw set.mem_set_of_eq at hx hy,
      unfold tag_is_next_after at hx hy,
      obtain ⟨hmx, hgx, hlx⟩ := hx,
      obtain ⟨hmy, hgy, hly⟩ := hy,
      have hgex, from hly x hmx hgx,
      have hgey, from hlx y hmy hgy,
      exact le_antisymm hgey hgex
    end

  -- The next tag for which a given event map has a scheduled event, 
  -- after a given "current" time.
  noncomputable def next_tag (μ : event_map υ) (c : tag) : option tag :=
    (next_tags_subsingleton μ c)
      .eq_empty_or_singleton
      .by_cases (λ _, none) (λ s, s.some)

end timed.network.event_map