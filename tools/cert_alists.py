"""Ask ACL2 whether cached certificate alists can compose.

The fn source-closure key is necessary but not sufficient: ACL2's book hash
also covers certification data and make-event expansion.  Read each candidate
with ACL2's own certificate reader, then compare the post-alist entry ACL2
requires for a child with that child's actual self entry.  Python only chooses
among the resulting exact ACL2 equality decisions; it does not parse or
reimplement certificate serialization.
"""
from __future__ import annotations

import os
from pathlib import Path
import re
import subprocess
import json


_MISSING_PACKAGE = re.compile(r'The name "([A-Za-z][A-Za-z0-9_-]{0,63})" '
                              r'does not designate any package')
_PAIR = re.compile(r"@@PAIR (\d+) (\d+) (T|NIL) (T|NIL)$", re.M)
_DONE = re.compile(r"@@DONE (\d+)$", re.M)
_UNREADABLE = re.compile(r"@@UNREADABLE (\d+)$", re.M)

_ACL2_DEFINITIONS = r'''
(in-package "ACL2")
(defun fn-ca-read-post (path state)
 (declare (xargs :stobjs state :mode :program))
 (mv-let (ch state) (open-input-channel path :object state)
  (if (not ch) (mv nil state)
   (mv-let (post state) (post-alist-from-channel nil nil ch state)
    (pprogn (close-input-channel ch state) (mv post state))))))
(defun fn-ca-read-many (paths n state)
 (declare (xargs :stobjs state :mode :program))
 (if (endp paths) (mv nil state)
  (mv-let (post state) (fn-ca-read-post (car paths) state)
   (mv-let (rest state) (fn-ca-read-many (cdr paths) (+ 1 n) state)
    (mv (cons (cons n post) rest) state)))))
(defun fn-ca-show-pairs (pairs data)
 (declare (xargs :mode :program))
 (if (endp pairs) nil
  (let* ((p (caar pairs))
         (c (cadar pairs))
         (parent (cdr (assoc-equal p data)))
         (child (cdr (assoc-equal c data)))
         (entry (and parent child
                     (assoc-familiar-name
                      (caddr (car child))
                      (unmark-and-delete-local-included-books (cdr parent)))))
         (required (and entry t))
         (okay (and parent child
                    (or (not entry)
                        (equal (cddr entry) (cddr (car child)))))))
   (prog2$ (cw "@@PAIR ~x0 ~x1 ~x2 ~x3~%" p c required okay)
           (fn-ca-show-pairs (cdr pairs) data)))))
(defun fn-ca-show-unreadable (data)
 (declare (xargs :mode :program))
 (if (endp data) nil
  (prog2$ (and (not (cdar data))
               (cw "@@UNREADABLE ~x0~%" (caar data)))
          (fn-ca-show-unreadable (cdr data)))))
'''


def _driver(paths: list[Path], pairs: list[tuple[int, int]],
            packages: list[str]) -> str:
    # ACL2's ordinary certificate reader needs symbol packages that a book's
    # portcullis would create.  The alist reader skips that portcullis, so a
    # missing package is declared locally in this read-only probe process.
    declarations = "".join(f'(defpkg "{name}" nil)\n' for name in packages)
    # The first form must enter ACL2's package before declarations.
    definitions = _ACL2_DEFINITIONS.replace('(in-package "ACL2")\n',
                                              '(in-package "ACL2")\n' + declarations,
                                              1)
    path_form = "(" + " ".join(json.dumps(str(path)) for path in paths) + ")"
    pair_form = "(" + " ".join(f"({p} {c})" for p, c in pairs) + ")"
    return (definitions
            + f"(make-event (mv-let (data state) (fn-ca-read-many '{path_form} 0 state) "
              f"(value (prog2$ (fn-ca-show-unreadable data) "
              f"(prog2$ (fn-ca-show-pairs '{pair_form} data) "
              f"(prog2$ (cw \"@@DONE ~x0~%\" {len(pairs)}) "
              "'(value-triple :ok)))))))\n"
            + "(quit)\n")


def acl2_certificate_pairs(paths: list[Path], pairs: list[tuple[int, int]],
                           acl2: Path, root: Path,
                           timeout_seconds: int = 120
                           ) -> dict[tuple[int, int], tuple[bool, bool]]:
    """Return `(required, equal)` for every parent/child candidate pair.

    Fail closed if ACL2 cannot read any certificate or does not report every
    requested pair.  No local certificate or cache entry is modified.
    """
    if not pairs:
        return {}
    if any(p < 0 or c < 0 or p >= len(paths) or c >= len(paths)
           for p, c in pairs):
        raise ValueError("certificate comparison index out of range")
    packages: list[str] = []
    environment = os.environ.copy()
    environment["ACL2_CUSTOMIZATION"] = "NONE"
    environment["ACL2_BOOK_HASH_ALISTP"] = "NIL"
    environment.pop("ACL2_SYSTEM_BOOKS", None)
    for _ in range(25):
        result = subprocess.run([str(acl2)], cwd=root,
                                input=_driver(paths, pairs, packages).encode(),
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                env=environment, check=False,
                                timeout=timeout_seconds)
        output = result.stdout.decode("utf-8", "replace")
        missing = _MISSING_PACKAGE.search(output)
        if missing:
            name = missing.group(1)
            if name in packages:
                raise ValueError("ACL2 repeatedly refused certificate package " + name)
            packages.append(name)
            continue
        done = _DONE.findall(output)
        if _UNREADABLE.search(output):
            raise ValueError("ACL2 could not read a cached certificate alist: "
                             + output[-1800:])
        found = {(int(p), int(c)): (required == "T", okay == "T")
                 for p, c, required, okay in _PAIR.findall(output)}
        if result.returncode or done != [str(len(pairs))] or len(found) != len(pairs):
            raise ValueError("ACL2 certificate-alist probe failed: " + output[-1800:])
        return found
    raise ValueError("ACL2 certificate-alist probe exceeded package retry bound")
