"""Extract the actual two native close functions for a recording regression."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parents[3]
out = Path(__file__).resolve().parent
source = (root / "host/native/io.lisp").read_text()


def take(name):
    start = source.index("(defun " + name + " ")
    depth = 0
    string = comment = escape = False
    for i in range(start, len(source)):
        c = source[i]
        if comment:
            if c == "\n":
                comment = False
            continue
        if string:
            if escape:
                escape = False
            elif c == "\\":
                escape = True
            elif c == '"':
                string = False
            continue
        if c == ";":
            comment = True
        elif c == '"':
            string = True
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return source[start : i + 1]
    raise RuntimeError(name)


forms = {name: take(name) for name in ("fnn-log-discard-spare", "fnn-store-close")}
prefix = '''(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defconstant +fnn-lock-un+ 8)
(defstruct fnn-log fd spare)
(defstruct fnn-store log lock-fd completion-pending recovery-identity recovery-source)
(defvar *calls* nil)
(defvar *failure* nil)
(defun fnn-close (fd)
 (push (list :close fd) *calls*)
 (when (eql fd *failure*) (error "recorded close uncertainty")))
(defun fnn-flock (fd mode)
 (push (list :flock fd mode) *calls*)
 (when (eq *failure* :unlock) (error "recorded unlock uncertainty")))
(defun fnn-lstat (path) (declare (ignore path)) t)
(defun fnn-unlink (path) (push (list :unlink path) *calls*))
'''
(out / "actual-close.lisp").write_text(
    prefix + "\n".join(forms.values()) + "\n" + (out / "cases.lisp").read_text()
)
(out / "coordinate.json").write_text(json.dumps({
    "source": "host/native/io.lisp",
    "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
    "functions": {name: hashlib.sha256(form.encode()).hexdigest() for name, form in forms.items()},
    "scope": "Literal native close functions; recording structures and filesystem calls. No image, physical-close, disk, or ACL2 proof claim."
}, indent=2) + "\n")
