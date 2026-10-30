; Writes D3's interim decision table (books/conn-answer.lisp, *fn2-answer-interim*)
; for the surface harness: one INTERIM line per command, its keyword, the
; reply's code and text from the grammar's declaration row, and the quest
; that replaces it. tests/conn-interim-json.py turns the lines into
; fn2/tests/surface/fn2_conn_interim.json:
;   tools/acl2 < fn2/tests/conn-interim-export.lsp | python3 fn2/tests/conn-interim-json.py
(in-package "ACL2")
(set-cbd "fn2/tests/")
(include-book "../books/conn-answer")
(set-inhibit-output-lst '(proof-tree prove event summary observation warning))
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(defun fn2-cie-lines (rows world)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (let* ((cmd (car (car rows)))
           (decl (fn2-decl-row (list :command (fn2-gram-sym 'fn2-nntp "-" cmd)) world))
           (reply (assoc-eq (cadr (car rows)) (fn2-decl-get :replies decl)))
           (plist (cdr reply)))
      (prog2$ (cw "INTERIM ~s0|~x1|~s2|~s3~%" (fn2-decl-get :keyword decl) (fn2-decl-get :code plist)
                  (fn2-decl-get :text plist) (symbol-name (caddr (car rows))))
              (fn2-cie-lines (cdr rows) world)))))
(make-event (prog2$ (fn2-cie-lines *fn2-answer-interim* (w state)) (value '(value-triple :done))))
(good-bye)
