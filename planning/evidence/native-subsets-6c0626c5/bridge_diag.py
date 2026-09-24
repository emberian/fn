# Diagnostic only: what does the Python ACL2 bridge answer for trivial forms
# that the consumer_e2 signed-poll check composes?
from tools import run_store
b = run_store.Acl2Store()
try:
    for form in ("(fn-stmt-okp nil)", "(fn-record-result-okp nil)",
                 "(fn-stxa-bindsp nil)", "(fn-stxa-decode-exact nil)"):
        out = b.call(form)
        print(form, "=>", repr(out[-600:]), flush=True)
finally:
    b.close()
