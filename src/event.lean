import order.lexicographic
import network.ids

def tag := lex ℕ ℕ  
def tag.time_val (t : tag) := t.1 
def tag.micros_idx (t : tag) := t.2 

inductive origin
  | logical : origin
  -- | physical : origin

structure action :=
  (id : empty) -- needed ?
  (delay : ℕ)
  (origin : origin)

structure event :=
  (trigger : reaction.id)
  (trig_value : option value)
  (tag : tag)
  