import ReactorModel.Inst.PrecGraph

open Reactor
open Ports

namespace Inst

variable {ι υ} [ID ι] [Value υ]

-- The parameter `orig` is the ID of the reaction from which this change was initiated.
-- This is required to ensure that mutations stay within their reactor.
def applicationOfChange (σ₁ σ₂ : Reactor ι υ) (orig : ι) : Change ι υ → Prop
  | Change.port i v =>  σ₁ -[Cmp.prt, i := v]→ σ₂ -- Port propagation isn't necessary/possible, because we're using relay reactions. 
  
  | Change.state i v => σ₁ -[Cmp.stv, i := v]→ σ₂

  -- "Connecting" means inserting a relay reaction.
  -- A mutation can only connect ports that are in its input- and output-dependencies, 
  -- as well as ports that belong to one of its children.
  --
  -- The objects and IDs used below correspond to this illustration:
  -- The outer box is a reactor and the boxes within the colons are nested reactors.
  -- The mutation (m) that triggered this change lives in the outer reactor.
  -- The relay reaction (i) that will be created lives in the same reactor.
  -- The src and dst ports can have multiple possible positions, and hence appear
  -- multiple times in the illustration.
  --     ______________________________________________
  --    |iₚ/p₁  :   _______             _______    :   |
  --    |       :  |       |           |       |   :   |
  --    |>src   :  |    src|>          |>dst   |   :   |
  --    |       :  |_______|           |_______|   :   |
  --    |       :                                  :   |
  --    |       ....................................   |
  --    |   ______            ____                     |
  --    |  |orig/m|     ...--|i   |--...               |>dst
  --    |  |______|          |____|                    |
  --    |______________________________________________|
  --
  -- NOTE: 
  -- We need to ensure that the added connection does not lead to input ports having more than one incoming connection.
  -- This is a good example of the conflict of where to place constraints:
  -- 1) `Reactor`s can have the constraint that input ports have to be uniquely connected.
  -- 2) Execution can add a constraint ensuring that new connections maintain input port connection uniqueness.
  -- The first option is probably necessary anyway to ensure that reactors are well-formed before execution.
  -- The second option is then redundant, as the `applicationOfChange` relation with `connect` as change, will only
  -- be satisfiable if the input port connection uniqueness is maintained (because otherwise `σ₂` could not exist).
  --
  -- TODO: Check that the precendence graph of `σ₁` and `σ₂` are the same? (Marten's Thesis, Algorithm 7, Line 20)
  | Change.connect src dst =>
    ∃ (iₚ i : ι) (m : Reaction ι υ) (p₁ p₂ : Reactor ι υ), 
      σ₁ *[Cmp.rtr] iₚ = p₁ ∧                               
      σ₁ & orig = iₚ ∧
      p₁.rcns orig = m ∧
      let mChildPorts : Ports.Role → Finset ι := λ r => (σ₁ *[Cmp.rtr] m.children).bUnion (λ rtr => (rtr.ports' r).ids) -- TODO: Factor this into a definition of its own.
      src ∈ (m.deps Role.in  ∪ mChildPorts Role.out) ∧       -- The src port must be a dependency of m, or an output-port of one of its children.
      dst ∈ (m.deps Role.out ∪ mChildPorts Role.in) ∧        -- The dst port must be an antidependency of m, or an input-port of one of its children.
      (i ∉ p₁.rcns.ids) ∧                                    -- Checks that i is an ununsed ID in p₁'s set of reactions, so no overriding occurs. 
      p₂.rcns = p₁.rcns.update' i (Reaction.relay src dst) ∧ -- Inserts the required relay reaction.
      p₂.prios = p₁.prios.withIncomparable i ∧               -- Sets the priority of the relay reaction to *.
      p₂.ports = p₁.ports ∧ p₂.roles = p₁.roles ∧ p₂.state = p₁.state ∧ p₂.nest = p₁.nest ∧ 
      σ₁ -[Cmp.rtr, iₚ := p₂]→ σ₂

  -- "Disconnecting" means checking whether src and dst are connected by a relay reaction,
  -- and if so removing that reaction.
  -- A mutation can only disconnect ports that are in its input- and output-dependencies, 
  -- as well as ports that belong to one of its children.
  -- 
  -- The objects and IDs used below correspond to this illustration:
  -- The outer box is a reactor, the boxes within the colons are nested reactors.
  -- The mutation (m) that triggered this change lives in the outer reactor.
  -- The relay reaction (iᵣ) that will be removed lives in the same reactor.
  -- The src and dst ports can have multiple possible positions, and hence appear
  -- multiple times in the illustration.
  --     ______________________________________________
  --    |iₚ/p₁  :   _______             _______    :   |
  --    |       :  |       |           |       |   :   |
  --    |>src   :  |    src|>          |>dst   |   :   |
  --    |       :  |_______|           |_______|   :   |
  --    |       :                                  :   |
  --    |       ....................................   |
  --    |   ______            ____                     |
  --    |  |orig/m|     ...--|iᵣ  |--...               |>dst
  --    |  |______|          |____|                    |
  --    |______________________________________________|
  | Change.disconnect src dst =>
    ∃ (iₚ iᵣ : ι) (m : Reaction ι υ) (p₁ p₂ : Reactor ι υ), 
      σ₁ *[Cmp.rtr] iₚ = p₁ ∧
      σ₁ & orig = iₚ ∧
      p₁.rcns orig = m ∧
      let mChildPorts : Ports.Role → Finset ι := λ r => (σ₁ *[Cmp.rtr] m.children).bUnion (λ rtr => (rtr.ports' r).ids) -- TODO: Factor this into a definition of its own.
      src ∈ (m.deps Role.in  ∪ mChildPorts Role.out) ∧ -- The src port must be a dependency of m, or an output-port of one of its children.
      dst ∈ (m.deps Role.out ∪ mChildPorts Role.in) ∧  -- The dst port must be an antidependency of m, or an input-port of one of its children.
      σ₁.rcns iᵣ = some (Reaction.relay src dst) ∧     -- Makes sure there is a relay reaction from src to dst.
      p₂.rcns = p₁.rcns.update iᵣ none ∧               -- Removes the relay reaction.
      p₂.prios = p₁.prios ∧ p₂.ports = p₁.ports ∧ p₂.roles = p₁.roles ∧ p₂.state = p₁.state ∧ p₂.nest = p₁.nest ∧ 
      σ₁ -[Cmp.rtr, iₚ := p₂]→ σ₂

  -- The objects and IDs used below correspond to this illustration:
  -- The outer box is a reactor, the box within the colons is the new reactor
  -- and the box outside the colons is the mutation that initiated this change.
  --     ______________________
  --    |iₚ/p₁  :   _______  : | 
  --    |       :  |i/rtr  | : | 
  --    |       :  |_______| : |
  --    |       :            : |
  --    |       .............. |
  --    |    ______            |
  --    |   |orig/m|           |
  --    |   |______|           |
  --    |______________________|
  --  
  -- TODO: Make sure that all reactions in the new reactor that are triggered by the startup-trigger
  --       run during the current logical time. But only after all mutations of orig's parent have
  --       been executed.
  | Change.create rtr i =>
    ∃ (iₚ : ι) (p₁ p₂ : Reactor ι υ) (m : Reaction ι υ) (hₘ : m.isMut),
      σ₁ *[Cmp.rtr] iₚ = p₁ ∧
      σ₁ & orig = iₚ ∧
      p₁.rcns orig = m ∧
      let m' := m.updateChildren (m.children ∪ (Finset.singleton i)) hₘ -- Adds the ID of the new reactor to the children 
      p₂.rcns = p₁.rcns.update orig m' ∧                                -- of the mutation that caused this change.
      (i ∉ p₁.nest.ids) ∧                                               -- Checks that i is an ununsed ID in p₁'s set of nested reactors, so no overriding occurs. 
      p₂.nest = p₁.nest.update i rtr ∧                                  -- Adds the new reactor using ID i. 
      p₂.ports = p₁.ports ∧ p₂.roles = p₁.roles ∧ p₂.state = p₁.state ∧ p₂.prios = p₁.prios ∧ 
      σ₁ -[Cmp.rtr, iₚ := p₂]→ σ₂

  -- Deletion takes place mainly in the time-world.
  -- Hence, here we make sure that the conditions for deletion are met:
  -- The deleted reactor has to be nested in the reactor whose mutation triggered the deletion.
  -- Also, deletion propagates down the entire hierarchy of reactors nested in the deletion target.
  --
  -- The objects and IDs used below correspond to this illustration:
  -- The outer box is a reactor, the box within the colons is the new reactor
  -- and the box outside the colons is the mutation that initiated this change.
  --     _____________________
  --    |iₚ/p  :   _______  : | 
  --    |      :  |i/rtr  | : | 
  --    |      :  |_______| : |
  --    |      :            : |
  --    |      .............. |
  --    |    _____            |
  --    |   |orig |           |
  --    |   |_____|           |
  --    |_____________________|
  --  
  -- TODO: "Mark" i for deletion.
  --       Call DELETE (recursivley) on all nested reactors of d.
  --       Trigger all required shutdown reactions at the current time step.
  --       In the time-world, once the current instantaneous execution has completed,
  --       delete the reactor and remove all of its port-connections.
  | Change.delete i =>
    ∃ (iₚ : ι) (p d : Reactor ι υ),
      σ₁ *[Cmp.rtr] iₚ = p ∧
      σ₁ & orig = iₚ ∧
      p.nest i = d

notation σ₁:max " -[" c ", " orig "]→ " σ₂:max => applicationOfChange σ₁ σ₂ orig c

def applicationOfOutput (σ₁ σ₂ : Reactor ι υ) (orig : ι) : List (Change ι υ) → Prop
  | [] => σ₁ = σ₂
  | hd::tl => ∃ σₘ, (σ₁ -[hd, orig]→ σₘ) ∧ (applicationOfOutput σₘ σ₂ orig tl)

notation σ₁:max " -[" o ", " orig "]→ " σ₂:max => applicationOfOutput σ₁ σ₂ orig o

def execOfRcn (σ₁ σ₂ : Reactor ι υ) (i : ι) : Prop :=
  ∃ (iₚ : ι) (ctx : Reactor ι υ) (rcn : Reaction ι υ),
    σ₁ & i = iₚ ∧
    σ₁ *[Cmp.rtr] iₚ = ctx ∧
    ctx.rcns i = rcn ∧
    let out := rcn (ctx.ports' Role.in % rcn.deps Role.in) ctx.state
    σ₁ -[out, i]→ σ₂

notation σ₁ " -[" rcn "]→ " σ₂:max => execOfRcn σ₁ σ₂ rcn

def execOfQueue (σ₁ σ₂ : Reactor ι υ) : List ι → Prop
  | [] => σ₁ = σ₂
  | hd::tl => ∃ σₘ, (σ₁ -[hd]→ σₘ) ∧ (execOfQueue σₘ σ₂ tl)
  
notation σ₁:max " -[" q "]→ " σ₂:max => execOfQueue σ₁ σ₂ q

inductive exec (σ₁ σ₂ : Reactor ι υ) (remIn remOut : List ι) : Prop
  -- An execution is *short* if it does not cross the boundary of a logical
  -- time step. That is, it only processes reactions from the input remainer (`remIn`)
  -- and does not require the generation of a new reaction queue.
  | short (_ :
      -- TODO: 
      -- This definition enables a trivial partial execution: `l % σ₁ →ₑ σ₁ l`.
      -- Is this ok? If not, will `¬l.empty` solve it?
      ∃ (l : List ι),
        remIn = l ++ remOut ∧
        σ₁ -[l]→ σ₂
    )
  -- An execution is *long* if it crosses the boundary of a logical time step.
  -- That is, it processes all of the reactions from the input remainer (`remIn`),
  -- as well as reactions from the following new reaction queue.
  | long (_ :
      -- TODO:
      -- A consequence of requirement (1) is that the reactions enqueued in a
      -- remainder list can never be from different instantaneous exections.
      -- Hence, any (permitted) reordering within a remainder list will simply
      -- be equivalent to producing a different topological ordering of the
      -- precedence graph generated for that instantaneous step.
      -- So this probably enforces barrier synchronization again.
      -- On the other hand, if we want to allow the generation of a new precedence graph
      -- and derived reaction queue *before* all prior reactions have been executed,
      -- we probably need to figure out what constraints are required for this to be
      -- allowed. 
      -- Perhaps we only need to ensure that all previous mutations have run?
      -- Note, that figuring out when a new precedence graph can be created is not
      -- the same as figuring out in what way the time barrier can be crossed (i.e.
      -- in what way the remainder-queue can be reordered).
      -- If it is in fact the case that all previous mutations have to have run, 
      -- before we can create a new precedence graph, then this puts a bound on the
      -- time range of the reactions that can accumulate in the remainder queue.
      -- Specifically, (assuming requirement (1) will is resolved) they can only come
      -- from two consecutive instantaneous executions (unless we are able to reorder
      -- the remainder queue such that reactions can precede their mutations).
      -- The pattern being: [remaining rcns from step n, mutations from step n + 1, reactions from step n + 1].
      -- Perhaps this means that mutations enforce barrier sync - 
      -- unless we consider which mutations are actually triggered.
      -- E.g. assuming the following remainder queue:
      -- [a1, a2, a3, m1, m2, b1, b2, b3]
      -- Assuming that m1 and m2 are not triggered by the current port assigment,
      -- and additionally assuming that a1, a2 and a3 don't have a connection to m1 and m2,
      -- then we can deduce that m1 and m2 won't be triggered, therefore removing them from
      -- the queue. Aside from opening the possiblity for more reordering in the remainder queue,
      -- this also implies that we can generate a new prec graph.
      --
      -- Is it a problem, that all of the reactions are accumulating in *one* remainder queue?
      -- What happens when we ignore mutations?
      ∃ (σₘ : Reactor ι υ) (π : PrecGraph σₘ) (l : List ι),
        σ₁ -[remIn]→ σₘ ∧ -- (1) 
        π.isAcyclic ∧ 
        (l ++ remOut).isCompleteTopoOver π ∧  
        σₘ -[l]→ σ₂
    ) 

notation i:max " % " σ₁:max "→" σ₂:max " % " o:max => exec σ₁ σ₂ i o

end Inst