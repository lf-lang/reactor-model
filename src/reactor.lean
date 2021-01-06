import primitives
import reaction

open reactor
open reaction

-- It would be nice to declare reactors in a similar fashion to reactions.
-- I.e. reactions in themselves declare what they connect to (dᵢ and dₒ).
-- The difference is that reactions themselves are just a single "connection point",
-- so the mapping is a many-to-one (dependencies to reaction).
-- For reactors the mapping would have to be a many to many mapping (other reactors'
-- ports to own ports). This would on the one hand require the number of other reactors
-- to become part of a reactor's type, which seems inelegant. And further the mapping
-- would have to be implemented as a relation between another reactor's ports and the
-- self-reactor's ports. This would in turn also require nᵢ and nₒ to move into a 
-- reactor's type.

structure reactor :=
  {nᵢ nₒ nᵣ : ℕ}
  (input : ports nᵢ)
  (output : ports nₒ)
  (state : state_vars)
  (reactions : priority nᵣ → reaction)
  (rcn_dims : ∀ r, (∃ p, reactions p = r) → r.dim = (nᵢ, nₒ)) -- The ∃-term is just the explicit way of writing `r ∈ reactions`.

@[reducible]
instance : has_mem reaction reactor := {mem := λ rcn rtr, ∃ p, rtr.reactions p = rcn}

namespace reactor 

  -- A reactor is runnable iff all of it's reactions' bodies are functions.
  def is_runnable (r : reactor) : Prop :=
    ∀ rcn : reaction, rcn ∈ r → rcn.body.is_function

  -- A list of a given reactors reactions, ordered by their priority.
  def ordered_rcns (r : reactor) : list reaction :=
    let priorities := (fintype.elems (priority r.nᵣ)).sort (<) in
    priorities.map r.reactions

  -- A reaction is a member of a reactor's list of `ordered_reactions` iff it is also a member of
  -- the reactor itself.
  theorem ord_rcns_mem_rtr (rtr : reactor) :
    ∀ rcn : reaction, rcn ∈ rtr.ordered_rcns ↔ rcn ∈ rtr :=
    begin
      intro rcn,
      rw ordered_rcns,
      split,
        { 
          simp,
          intros p _ h,
          exact ⟨p, h⟩
        },
        {
          simp,
          intros p h,
          exact ⟨p, fintype.complete p, h⟩
        }
    end

  -- The dimensions of the reactions in a reactor's list of `ordered_reactions` are the same as the
  -- dimensions of the reactor itself.
  theorem ord_rcns_dims_eq_rtr_dims (rtr : reactor) : 
    ∀ rcn : reaction, rcn ∈ rtr.ordered_rcns → rcn.dim = (rtr.nᵢ, rtr.nₒ) :=
    begin
      intros rcn h,
      suffices hₘ : rcn ∈ rtr, from rtr.rcn_dims rcn hₘ,
      apply (ord_rcns_mem_rtr rtr rcn).mp h
    end

  -- If a given reactor is runnable, then all of its reactions' bodies are functions.
  theorem ord_rcns_runnable (rtr : reactor) (h : rtr.is_runnable) :
    ∀ rcn : reaction, rcn ∈ rtr.ordered_rcns → rcn.body.is_function :=
    begin
      intros rcn hₘ,
      apply h,
      apply (ord_rcns_mem_rtr rtr rcn).mp hₘ
    end

  noncomputable def priority_of (rtr : reactor) (rcn : reaction) (h : rcn ∈ rtr) : priority rtr.nᵣ := 
    h.some

  private def merge_ports {n : ℕ} (first last : ports n) : ports n :=
    λ i : fin n, (last i).elim (first i) (λ v, some v)

  private noncomputable def run_aux 
  {nᵢ nₒ : ℕ} (rs : list reaction) 
  (h_dim : ∀ r : reaction, r ∈ rs → r.dim = (nᵢ, nₒ))
  (h_fun : ∀ r : reaction, r ∈ rs → r.body.is_function) 
  (p : ports nᵢ) (s : state_vars) 
  : ports nₒ × state_vars :=
    list.rec_on rs.attach
      (ports.empty nₒ, s)
      (
        λ rₕ _ osₜ,
          let dim_rₕ : (rₕ : reaction).nᵢ = nᵢ := (prod.mk.inj (h_dim rₕ rₕ.property)).left in 
          let osₕ : ports nₒ × state_vars := 
            if (rₕ : reaction).fires_on p dim_rₕ then 
              let rₕ_fun := (rₕ : reaction).body.function (h_fun rₕ rₕ.property) in
              let os := rₕ_fun (p, s) in
              ⟨os.1, os.2⟩
            else 
              ⟨ports.empty nₒ, s⟩ 
          in
            ⟨merge_ports osₕ.1 osₜ.1, osₜ.2⟩
      )

  --* Technically it would be better to define a run-relation that can handle non-functional 
  --* reaction bodies, and then show that if the function-property is satisfied the run-relation is
  --* also a function. But that would be too time-intensive right now.
  noncomputable def run (r : reactor) (h : r.is_runnable) : reactor :=
    let os := run_aux r.ordered_rcns (ord_rcns_dims_eq_rtr_dims r) (ord_rcns_runnable r h) r.input r.state in
    {input := ports.empty r.nᵢ, output := os.1, state := os.2, ..r}

  theorem volatile_input (r : reactor) (h : r.is_runnable) : 
    (run r h).input = ports.empty r.nᵢ :=
    by refl 

  --? Prove the same for state.
  theorem no_in_no_out (r : reactor) (h : r.is_runnable) : 
    r.input = ports.empty r.nᵢ → (run r h).output = ports.empty r.nₒ :=
    sorry

  private lemma merge_empty_is_neutral {n : ℕ} (first last : ports n) :
    last = ports.empty n → (merge_ports first last) = first := 
    begin
      assume h,
      rw merge_ports,
      simp,
      rw [h, ports.empty],
      simp,
    end

  private lemma merge_skips_empty {n : ℕ} (first last : ports n) (i : fin n) :
    (last i) = none → (merge_ports first last) i = (first i) := 
    begin
      assume h,
      rw merge_ports,
      simp,
      rw h,
      simp,
    end

  -- Running a single unconnected reactor is deterministic, if it is runnable
  -- (cf. `reactor.is_runnable`) and if equal initial states lead to equal end states. 
  -- Since `reactor.run` is a function, determinism is trivially fulfilled.
  protected theorem determinism (r₁ r₂ : reactor) (h₁ : r₁.is_runnable) (h₂ : r₂.is_runnable) : 
    r₁ = r₂ → run r₁ h₁ = run r₂ h₂ :=
    begin
      intro h,
      subst h,
    end

end reactor
