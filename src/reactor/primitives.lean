import primitives

-- A reactor's state fields and ports are represented as maps from (a fixed set of) indices to
-- (possibly absent) values. Single ports and state fields can therefore be identified by values
-- of these maps' domains (i.e. indices).
--
--? It should be possible to extract the "core" of these definitions into a single definition and
--? then just have `ports` and `state` be typealiases for that core.
namespace reactor

  def ports (n : ℕ) := (fin n) → (option value)
  def state (n : ℕ) := (fin n) → (option value)

  def ports.absent {n : ℕ} : ports n := λ _, none

end reactor