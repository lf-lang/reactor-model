import basic

def origin := Type*

structure action :=
(identifier : identifier)
(delay : ℕ)
(origin : origin)

variable a : action

--⚡️ Actually the delay should be gotten from the identifier alone. 
--⚡️ But since that would require some kind of central source of truth to get an action from its identifier,
--⚡️ we also require the action implicitly, as well as a proof that the given identifier matches that action's identifier.
def d {a : action} (i : identifier) (h: a.identifier = i) : ℕ := a.delay

--! Cf. `d` above.
def o {a : action} (i : identifier) (h: a.identifier = i) : origin := a.origin