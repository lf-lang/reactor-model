# Whiteboard

Execution				| rfl
						| transitive exec steps

Execution.Step			| inst exec
						| advance time

CompleteInstExecution	| exec until complete

-------------------------------------------------------- DETERMINISM ATM					

InstExecution			| inst step												exposes: reaction list
						| transitive inst steps

InstStep				| change list step										exposes: reaction
						| skip rcn

ChangeListStep			| nil													exposes: reaction, change list
						| transitive change steps							

ChangeStep				| port update											exposes: reaction, change
						| state update
						| action update
						| mutation noop
				

