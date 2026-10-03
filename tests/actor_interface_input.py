"""Emit exact source declarations for the private runtime interface batch.

The reader only selects literal top-level forms; ACL2 validates their actual
loaded-world classes, guard kinds and literal theorem subjects.
"""
from pathlib import Path
from tools.ledger import Reader

source = Path("host/interfaces.lisp").read_text()
reader = Reader(source)
selected = []
while True:
    reader.skip_space()
    if reader.pos >= len(source):
        break
    start = reader.pos
    form = reader.form()
    if (isinstance(form, list) and len(form) > 1
            and str(form[0]) == "definterface"
            and (str(form[1]).startswith(("fn-oqw-", "fn-cmt-", "fn-fs-actor-", "fn-otb-"))
                 or str(form[1]) == "fn-fs-inbox-admit")):
        selected.append((str(form[1]), source[start:reader.pos]))

assert {"fn-oqw-step", "fn-oqw-outcome-of-final", "fn-cmt-step"} <= {x[0] for x in selected}
for book in ("owner-queued-work", "failure-scope", "committer-actor", "definterface"):
    print(f'(include-book "books/{book}")')
for name, text in selected:
    print(text)
    print(f"(assert-event (assoc-eq '{name} (table-alist 'fn-interfaces (w state))))")
print("""(make-event
 (if (and (fn-di-keystone-problem 'fn-oqw-step 'fn-oqw-batch-effect-order (w state))
          (fn-di-keystone-problem 'fn-oqw-outcome-of-final
                                 'fn-oqw-receipt-outcomes-are-distinct (w state)))
     '(value-triple :wrong-literal-subjects-refused)
   (er soft 'runtime-interface-batch "A wrong literal subject was accepted.")))""")
print(f'(value-triple :actor-interface-batch-pass-{len(selected)})')
print('(good-bye)')
