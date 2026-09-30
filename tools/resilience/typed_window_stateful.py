"""Bundle-based symbolic typed requests; generated trials require actual replay.

Workload choices belong to Hypothesis. A separately keyed fault stream chooses
wrong ticket/offset observations; it never manufactures native fault events.
"""
import hashlib
from .typed_window_model import Step, initial, transition
from .scenario import Operation, Scenario, check


def generate(consume, examples=6, steps=6, fault_seed=23):
    if type(examples) is not int or examples < 1 or type(steps) is not int or steps < 1:
        raise ValueError("positive example and step budgets required")
    from hypothesis import settings, strategies as st
    from hypothesis.stateful import Bundle, RuleBasedStateMachine, initialize, rule, run_state_machine_as_test

    class WindowMachine(RuleBasedStateMachine):
        requests = Bundle("requests")

        def __init__(self):
            super().__init__()
            self.steps = []
            self.state = initial()
            self.serial = 0

        def add(self, action, request="initial", selector="exact"):
            step = Step(f"op-{len(self.steps)}", action, request, selector)
            self.steps.append(step)
            self.state, _ = transition(self.state, step)

        @initialize(target=requests)
        def assigned(self):
            return "initial"

        @rule(target=requests)
        def admit(self):
            label = f"request-{self.serial}"
            self.serial += 1
            self.add("admit", label)
            if self.state["live"] == label:
                self.add("acquire", label)
            return label

        @rule(request=requests, action=st.sampled_from(("cancel", "return", "release", "settle")))
        def lifecycle(self, request, action):
            key = f"{fault_seed}:{len(self.steps)}:{action}:{request}".encode()
            selector = ("exact", "exact", "wrong-offset", "wrong-ticket")[hashlib.sha256(key).digest()[0] % 4]
            self.add(action, request, selector)

        def teardown(self):
            healing_start = len(self.steps)
            if self.state["live"] is not None:
                request = self.state["live"]
                self.add("cancel", request)
                self.add("return", request)
                self.add("settle", request)
            else:
                # The existing settlement remains a literal positive witness.
                self.add("settle")
            operations = [Operation(s.id, "core", "window-" + s.action,
                                    {"request": s.request, "selector": s.selector}) for s in self.steps]
            scenario = check(Scenario("typed-stateful", "Bundle symbolic typed request lifecycle",
                                      "typed-window-model", {"recipe": "typed-window-assigned-vector"},
                                      [{"name": "core", "kind": "client"}], operations, [],
                                      [s.id for s in self.steps[healing_start:]], ["typed-window-settled"],
                                      replay="exact"))
            consume(scenario)

    run_state_machine_as_test(WindowMachine,
        settings=settings(max_examples=examples, stateful_step_count=steps,
                          deadline=None, derandomize=True, database=None))
