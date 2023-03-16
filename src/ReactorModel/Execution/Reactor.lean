import ReactorModel.Objects
import ReactorModel.Execution.Action

noncomputable section
open ReactorType.Updatable

namespace Reactor

-- TODO: Find a better name for this.
--       * ID rtr cmp
--       * Obj rtr cmp
structure Valid (rtr : Reactor) (cmp : Component) where
  id    : ID
  valid : ∃ obj, rtr[cmp][id] = some obj

namespace Valid

instance {cmp} : Coe (Valid rtr cmp) ID where
  coe := Valid.id

def obj {cmp} (i : Valid rtr cmp) :=
  i.valid.choose

theorem obj?_id_eq_obj {cmp} (i : Valid rtr cmp) : rtr[cmp][i] = i.obj :=
  i.valid.choose_spec

def con {cmp} (i : Valid rtr cmp) : Identified Reactor :=
  ReactorType.Indexable.obj?_to_con?_and_cmp? i.obj?_id_eq_obj |>.choose

theorem con?_id_eq_con {cmp} (i : Valid rtr cmp) : rtr[cmp][i]& = i.con :=
  ReactorType.Indexable.obj?_to_con?_and_cmp? i.obj?_id_eq_obj |>.choose_spec.left

end Valid

def apply (rtr : Reactor) : Change → Reactor
  | .port k i v   => update rtr (.prt k) i (fun _ => v)
  | .state i v    => update rtr .stv     i (fun _ => v)
  | .action i t v => update rtr .act     i (·.schedule t v)
  | .mut ..       => rtr -- Mutations are currently no-ops.

def apply' (rtr : Reactor) (cs : List Change) : Reactor :=
  cs.foldl apply rtr

end Reactor