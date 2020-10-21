import basic
import tag

structure event := 
(event_trigger : identifier) 
(trigger_value : value)
(event_tag : tag)

namespace event

protected def lt (e₁ e₂ : event) : Prop := 
e₁.event_tag < e₂.event_tag

instance : has_lt event := ⟨event.lt⟩ 

-- protected def queue : list event := sorry

end event

