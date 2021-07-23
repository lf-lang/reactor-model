import lgraph

-- I THINK REACTORS MIGHT HAVE TO BE DEFINED AS AN INDUCTIVE FAMILY WHERE THE INDEX IS THE NESTING DEPTH
-- IN THE cntd_rtrs GRAPH. BECAUSE YOU CAN ONLY DEFINE A REACTOR OF NESTING DEPTH n IF YOU'VE DEFINED REACTORS
-- OF NESTING DEPTH n-1.
-- THE GRAPH TYPE ITSELF THEN ALSO HAS TO BE INDEXED. A GRAPH OF INDEX n CAN THEN ONLY HOLD REACTORS OF INDEX
-- n OR SMALLER. HOW THE "OR SMALLER" PART IS ACHIEVED I DON'T KNOW.
--
-- INSTEAD OF DEFINING reactor (I.E. A REACTOR WITH INDEX 0) IT MIGHT BE NICER TO DEFINE AN EMPTY GRAPH
-- (I.E. A GRAPH WITH INDEX 0) AS AN ATOMIC CONSTRUCTOR IN THE INDUCTIVE (FAMILY) DEFINITION.
-- THEN YOU CAN DEFINE THE INDEXED HIERARCHY OF REACTORS VERY NICELY, SUCH THAT EACH REACTOR CONTAINS 
-- A GRAPH OF THE SAME INDEX. 
--
-- THIS ALSO SOLVES THE PROBLEM OF HAVING TO DEFINE A "STUB-GRAPH" TYPE.
-- THE GRAPH/NETWORK TYPE CAN SIMPLY BE DEFINED AS CURRENTLY, WITH THE ONLY DIFFERENCE BEING THAT IT CARRIES AN INDEX.
-- (POSSIBLY THE INDEX ALWAYS HAS TO BE CONSTRAINED TO BE > 0).

universes u v
variables (ι : Type u) (υ : Type v)

structure network.edge := 
  (src : ι)
  (dst : ι)

instance lgraph_edge : lgraph.edge (network.edge ι) ι := 
  ⟨network.edge.src, network.edge.dst⟩

inductive selection 
  | mut_out | mut | rcn | rtr | network : rtrcl
  
inductive reactor_component: rtrcl → Type (max u v)
  | empty_mutation_output /-no reactors that can be created -/ : reactor_component rtrcl.mut_out
  | mutation_output {d : ℕ} : reactor_component rtrcl.mut_out
  | mutation {d : ℕ} : reactor_component rtrcl.mut
  | reaction {d : ℕ} : reactor_component rtrcl.rcn
  | reactor [decidable_eq ι] [reactor.value υ]
      {d : ℕ}
      (prts : ports.role → ports ι υ) 
      (state : state_vars ι υ)
      -- (rcns : ι ⇀ reactor_component rtrcl.rcn d)
      -- (muts : ι ⇀ reactor_component rtrcl.mut d)
      -- (prio_rel : partial_order ι)
      -- (nest : reactor_component rtrcl.network d)
      -- (wf_rcn_deps : ∀ {rcn : reaction d} (h : rcn ∈ rcns.values) (r : ports.role), (rcn.deps r) ⊆ (prts r).ids)
      -- (wf_mut_deps : ∀ {m : mutation d} (h : m ∈ muts.values) (r : ports.role), (m.deps r) ⊆ (prts r).ids)
      : reactor_component rtrcl.rcn
  | empty_network : reactor_component rtrcl.network
  | network 
      {d : ℕ}
      -- (g : lgraph ι (reactor_component rtrcl.rtr d) (network_edge ι)) 
      : reactor_component rtrcl.network