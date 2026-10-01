"""Regression checks actual producer forms against the INITIAL consumer."""
from pathlib import Path
import re
import sys
root = Path(__file__).resolve().parents[1]
producer = Path(sys.argv[1]) if len(sys.argv) > 1 else root / "books/runtime-operation-source.lisp"
text = producer.read_text()
consumer = (root / "host/snapshot-initial-host.lisp").read_text()
for name, payload in [("fn-owner-runtime-operation-source", "family"),
                      ("fn-owner-runtime-operation-role-table", "roles")]:
    start = text.index("(defun " + name + " ")
    end = text.find("\n(defun ", start + 1)
    form = text[start:end if end >= 0 else len(text)]
    returned = re.search(r"\(mv (:[\w-]+) " + payload + r"\)", form).group(1)
    call = consumer.index("(" + name + " :initial")
    check = re.search(r"\(eq word (:[\w-]+)\)", consumer[call:]).group(1)
    assert check == returned, (name, returned, check)
    assert ":runtime-operation-unavailable" in form
print("Actual runtime getter/INITIAL status boundaries match (2); unavailable preserved.")
