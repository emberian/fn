; Writes the declared NNTP command table for tests/grammar-oracle.py, one
; GRAMMAR-ROW per command: (keyword args states block help spec reply-codes).
;   tools/acl2 < fn2/tests/grammar-export.lsp > build/nntp-grammar-table.txt
(in-package "ACL2")
(set-cbd "fn2/tests/")
(include-book "grammar-unit")
(set-inhibit-output-lst '(proof-tree prove event summary observation warning))
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(defun fn2-ge-print (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (prog2$ (cw "GRAMMAR-ROW ~x0~%" (car rows)) (fn2-ge-print (cdr rows)))))
(value-triple (fn2-ge-print *fn2-gu-table*))
(value-triple (cw "GRAMMAR-HELP ~x0~%" *fn2-nntp-help-text*))
;; Argument-validator verdicts on a fixed generated sample (seeded 20261029),
;; checked by the oracle against the model's MSGID, number_range and wildmat.
(defconst *fn2-ge-samples*
  (quote ((:msgid "<a@b>" "<>" "<a>" "a@b" "<a b>" "<xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx>" "<xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx>" "<a>b>" "<ab>" "<a~b>" "<@>" "<a@[1.2]>" "<<a>" "<a>>" "<=>" "<?>" "<!>" "!]1,.10<" "<[*-" "@01" "[*1200" "!30@!2[b" "1<,-@?," "!<*1<" ",2b" ",3" ".?,b]" "-" ",>.?!" "1]0?3--[" "a")
    (:range "1" "0" "2147483647" "2147483648" "1-" "1-5" "5-1" "-5" "1--2" "01" "0000000000000001" "00000000000000001" "1-2147483648" "12-" "a" "1-a" "1-0" "*@0!3" "?--33>>." "?0a2b3,0" "13,.a" "]<.>a--" ">]aa2" "a1!." "3-," "b[*ba.b<" "3<>-" ">*a<@b1" "a031!2*@" "0b")
    (:wildmat "*" "a*" "!a" "a,!b" "a,,b" "a," "!" "a!b" "a[b" "a]b" "a\\\\b" "comp.*,!comp.sys.*,comp.sys.mac" "?" "*,!*" "a,b,c" "x!" "*]>" ">-2,0" "[@11,.]<" "!2*[[@*" "<[" "!b<[" ">]-><b01" ".0-.." "a" "0" "??3@>>" "<[>,?" "*0.."))))
(defun fn2-ge-verdict (kind str)
  (declare (xargs :verify-guards nil))
  (let ((octets (fn2-gu-text str)))
    (with-local-stobj fn2-pool
      (mv-let (ok fn2-pool)
        (let ((fn2-pool (fn2-pool-init '((1 . 4096)) 1 1000 fn2-pool)))
          (mv-let (c slot gen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool)
            (declare (ignore c))
            (mv-let (rest fn2-pool) (fn2-nntp-feed (len octets) octets slot gen fn2-pool)
              (declare (ignore rest))
              (mv-let (ok form a b) (fn2-gram-arg kind 0 (len octets) slot gen 1 1 1 fn2-pool)
                (declare (ignore form a b))
                (mv ok fn2-pool)))))
        ok))))
(defun fn2-ge-samples (kind strs)
  (declare (xargs :verify-guards nil))
  (if (atom strs) nil
    (prog2$ (cw "GRAMMAR-SAMPLE ~x0~%" (list kind (car strs) (if (fn2-ge-verdict kind (car strs)) t nil)))
            (fn2-ge-samples kind (cdr strs)))))
(defun fn2-ge-all-samples (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil (prog2$ (fn2-ge-samples (caar rows) (cdar rows)) (fn2-ge-all-samples (cdr rows)))))
(value-triple (fn2-ge-all-samples *fn2-ge-samples*))
(value-triple (cw "GRAMMAR-END~%"))
(good-bye)
