; Prints layer A's declaration registry (the world tables the DSL forms write)
; as one S-expression, for fn2/meta/emit/emit_lean.py. Ordinary top-level I/O,
; never a certifying event (the pattern of fn2/tools/owed-export.lsp).
; Run from the worktree root after `fn2/tools/certify.sh books/reference.lisp`:
;   fn2/meta/emit/emit.sh
(in-package "ACL2")
(include-book "fn2/books/reference")
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(mv-let (channel state)
        (open-output-channel "fn2/meta/emit/registry.sexp" :character state)
  (if (not channel)
      (prog2$ (er hard 'fn2-meta-print-registry "Cannot write fn2/meta/emit/registry.sexp.") state)
    (let* ((wrld (w state))
           ; TABLE-ALIST is newest first; reverse gives declaration order.
           (registry
            (list :fn2-registry
                  (list :machine-kinds (reverse (table-alist 'fn2-machine-kinds wrld)))
                  (list :columns (reverse (table-alist 'fn2-columns wrld)))
                  (list :core-children (reverse (table-alist 'fn2-core-children wrld)))
                  (list :owed (reverse (table-alist 'fn2-owed wrld)))
                  (list :core-instance (table-alist 'fn2-core-instance wrld))))
           (state (fms! "~x0~%" (list (cons #\0 registry)) channel state nil))
           (state (close-output-channel channel state)))
      (prog2$ (cw "FN2-META-PRINT-REGISTRY PASS~%") state))))
