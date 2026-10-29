; Materialize dispatch after all registered continuations.
(in-package "ACL2")
(include-book "assembly-callbacks")
(fn2-machine-dispatch-events)
