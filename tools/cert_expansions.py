"""The definitions a certified book's make-events produced, read from its certificate.

A book's `.cert` records every `make-event` expansion (its :EXPANSION-ALIST):
the form ACL2 itself evaluated to define a generated function.  This module
asks ACL2's own certificate reader for those expansions of a book whose cached
certificate is CURRENT -- a cache entry at the book's present closure key, the
rule `green_check` uses for "certified" -- and returns each generated
definition as text.  Python parses nothing of the serialization: ACL2 reads the
certificate and prints the `defun`s it finds in the expansion; Python only
splits the printed text per definition.

A book with no entry at its current closure key (a missing cert, or one made
from other bytes) has NO answer here, never a guess.
"""
from __future__ import annotations

from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import acl2_slots  # noqa: E402
import cert_alists  # noqa: E402
import cert_images  # noqa: E402
import certs  # noqa: E402

_DONE = re.compile(r"^@@DONE (\d+)$", re.M)
_UNREADABLE = re.compile(r"^@@UNREADABLE (\d+)$", re.M)

_DEFINITIONS = r'''
(in-package "ACL2")
(defun fn-ce-read-next (ch state)
 (declare (xargs :stobjs state :mode :program))
 (mv-let (eofp obj state) (read-object ch state)
  (mv (not eofp) obj state)))
(defun fn-ce-skip-to-end-portcullis (ch state)
 (declare (xargs :stobjs state :mode :program))
 (mv-let (eofp obj state) (read-object ch state)
  (cond (eofp (mv nil state))
        ((eq obj :end-portcullis-cmds) (mv t state))
        (t (fn-ce-skip-to-end-portcullis ch state)))))
; (mv status alist state): status :none when the certificate records no
; make-event expansion (ACL2 writes :cert-data instead), :alist, or nil when
; the file is no certificate.
(defun fn-ce-skip-to-expansions (ch state)
 (declare (xargs :stobjs state :mode :program))
 (mv-let (ok state) (fn-ce-skip-to-end-portcullis ch state)
  (if (not ok) (mv nil nil state)
   (mv-let (eofp obj state) (read-object ch state)
    (cond (eofp (mv nil nil state))
          ((eq obj :expansion-alist)
           (mv-let (eofp2 alist state) (read-object ch state)
            (if eofp2 (mv nil nil state) (mv :alist alist state))))
          (t (mv :none nil state)))))))
(mutual-recursion
(defun fn-ce-walk (x)
 (declare (xargs :mode :program))
 (cond ((atom x) nil)
       ((eq (car x) 'record-expansion)
        (and (consp (cdr x)) (consp (cddr x)) (fn-ce-walk (caddr x))))
       ((and (member-eq (car x) '(defun defund defun-nx defund-nx defun-inline
                                  defund-inline defun-notinline defun$))
             (consp (cdr x)) (symbolp (cadr x)))
        (cw "~%@@DEFUN ~x0 ~x1~%" (cadr x) x))
       (t (fn-ce-walk-list x))))
(defun fn-ce-walk-list (x)
 (declare (xargs :mode :program))
 (if (consp x)
     (prog2$ (fn-ce-walk (car x)) (fn-ce-walk-list (cdr x)))
   nil)))
(defun fn-ce-walk-alist (alist)
 (declare (xargs :mode :program))
 (if (consp alist)
     (prog2$ (and (consp (car alist)) (fn-ce-walk (cdar alist)))
             (fn-ce-walk-alist (cdr alist)))
   nil))
(defun fn-ce-read (path n state)
 (declare (xargs :stobjs state :mode :program))
 (mv-let (ch state) (open-input-channel path :object state)
  (if (not ch)
      (prog2$ (cw "~%@@UNREADABLE ~x0~%" n) (mv nil state))
   (mv-let (found alist state) (fn-ce-skip-to-expansions ch state)
    (pprogn (close-input-channel ch state)
            (prog2$ (if found
                        (prog2$ (cw "~%@@BOOK ~x0~%" n)
                                (if (eq found :alist) (fn-ce-walk-alist alist) nil))
                      (cw "~%@@UNREADABLE ~x0~%" n))
                    (mv nil state)))))))
(defun fn-ce-read-many (paths n state)
 (declare (xargs :stobjs state :mode :program))
 (if (endp paths) (mv nil state)
  (mv-let (x state) (fn-ce-read (car paths) n state)
   (declare (ignore x))
   (fn-ce-read-many (cdr paths) (+ 1 n) state))))
'''


def _driver(paths: list[Path], packages: list[str]) -> str:
    declarations = "".join(f'(defpkg "{name}" nil)\n' for name in packages)
    definitions = _DEFINITIONS.replace('(in-package "ACL2")\n',
                                       '(in-package "ACL2")\n' + declarations, 1)
    path_form = "(" + " ".join('"%s"' % str(p).replace("\\", "\\\\").replace('"', '\\"')
                               for p in paths) + ")"
    return (definitions
            + f"(make-event (mv-let (x state) (fn-ce-read-many '{path_form} 0 state) "
              f"(declare (ignore x)) (value (prog2$ (cw \"~%@@DONE {len(paths)}~%\") "
              "'(value-triple :ok)))))\n(quit)\n")


def read_expansions(paths: list[Path], acl2: str, root: Path,
                    timeout: int = 300) -> list[dict[str, str]]:
    """One {name: defun text} per certificate, in PATHS' order, from ACL2."""
    packages = list(cert_alists._KNOWN_PACKAGES)
    for _ in range(25):
        done = acl2_slots.run([acl2], "cert_expansions", cwd=root,
                              input=_driver(paths, packages).encode(),
                              stdout=__import__("subprocess").PIPE,
                              stderr=__import__("subprocess").STDOUT,
                              check=False, timeout=timeout)
        output = done.stdout.decode("utf-8", "replace")
        missing = cert_alists._MISSING_PACKAGE.search(output)
        if missing:
            name = missing.group(1)
            if name in packages:
                raise ValueError("ACL2 repeatedly refused certificate package " + name)
            packages.append(name)
            if name not in cert_alists._KNOWN_PACKAGES:
                cert_alists._KNOWN_PACKAGES.append(name)
            continue
        if _UNREADABLE.search(output) or _DONE.findall(output) != [str(len(paths))] or done.returncode:
            raise ValueError("ACL2 could not read a certificate's expansions: " + output[-1800:])
        return _split(output, len(paths))
    raise ValueError("ACL2 certificate-expansion probe exceeded package retry bound")


def _split(output: str, count: int) -> list[dict[str, str]]:
    """The printed `@@BOOK n' / `@@DEFUN name form' stream, per certificate.
    A printed form may wrap, so a definition runs to the next marker."""
    books: list[dict[str, str]] = [{} for _ in range(count)]
    current = None
    name = None
    chunks: list[str] = []

    def close():
        if current is not None and name is not None:
            books[current][name] = " ".join(chunks)

    for line in output.splitlines():
        if line.startswith("@@BOOK "):
            close()
            current, name, chunks = int(line.split()[1]), None, []
        elif line.startswith("@@DEFUN "):
            close()
            _, name, rest = line.split(" ", 2)
            name, chunks = name.lower(), [rest]
        elif line.startswith("@@DONE"):
            close()
            name = None
        elif name is not None:
            chunks.append(line)
    return books


def current_cert(root: Path, book: str, cache: Path | None = None) -> Path | None:
    """The cached `book.cert` at BOOK's current closure key (any world the
    image rule allows for it now), newest first; None when there is none.
    BOOK is `books/NAME`.  An entry whose bytes fail its metadata is never
    returned (certs.cached_entries' integrity check)."""
    cache = cache or certs.cache_directory()
    try:
        entries = certs.book_entries(root, cache, book)
    except (certs.UnreadableBook, cert_images.UnreadableSource, OSError):
        return None
    entries = [(directory, meta) for directory, meta in entries
               if (directory / "book.cert").is_file()]
    if not entries:
        return None
    entries.sort(key=lambda e: str(e[1].get("published_at", "")), reverse=True)
    return entries[0][0] / "book.cert"
