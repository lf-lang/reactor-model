import data.set
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

  protected def queue := list event

  namespace queue 

    -- Read chapter 8 so you can implement this.
    private def peek' : event → event.queue → event
    | e nil := e
    | e (list.cons e' q') := peek' sorry sorry

    begin
      induction q,
        case nil { exact e },
        case cons :  { 
          sorry
        }
    end

    def peek (q : event.queue) : option event := 
    begin
      cases q,
        case nil         { exact none },
        case cons : e q' { exact some (peek' e q') }
    end

  end queue

end event

