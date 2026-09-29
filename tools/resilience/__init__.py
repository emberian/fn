"""fn's model-based resilience framework (planning/design-resilience-framework-2026-09-29.md).

One scenario language (`scenario`), three separately recorded histories
(`journal`), one contract model that cites the theorems it transcribes
(`contract`), one whole-history checker whose verdict is never "valid" past
its budget (`checker`), the tester-of-testers mutations (`mutations`), the
schedule points of the review as generated scenarios (`schedule_points`),
and the backends' adapters (`adapters`).  No fn semantics live in Python
beyond the contract model the checker interprets; the facts it narrows on
come from the client, the environment and, where a book decides, the image.
"""

IR_VERSION = 2
CHECKER_VERSION = "resilience-checker/2"
