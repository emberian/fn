; Literal carried row boundary witnesses, not persistence/host activation evidence.
(in-package "ACL2")
(include-book "substrate-committed-transcript-tests")
(include-book "../../books/substrate-committed-row")
(defattach fn-digest fn-toy-mix-digest)
(make-event
 (list 'defconst '*stcet-row*
       (list 'quote
             (fn-held-make 0 1 0 "<row@example.invalid>" 0 '("fn.test")
                           "o" "s" "e" 1 0 (fn-hf-make 0 nil 0 nil)
                           (fn-hc-make (fn-stx-make-verdict :verified nil 0)
                                       (list *stcet-s1*) 0) nil nil))))
(assert-event (fn-held-p *stcet-row*))
(assert-event
 (and (or (fn-held-p *stcet-row*) (fn-hstxa-p *stcet-row*))
      (equal (fn-stce-row-start-carried *stcet-row*) (fn-stce-row-start *stcet-row*))))
(assert-event (equal (nth 1 (fn-stce-row-start-carried *stcet-row*)) (list *stcet-s1*)))
(assert-event (equal (nth 2 (fn-stce-row-start-carried *stcet-row*)) '("fn.test")))
(assert-event (fn-stce-cursor-shapep (fn-stce-row-start *stcet-row*)))
; Hypothesis-removal, corrupted row: source type is false; every retained
; premise (none) is satisfied; reference/carried equality fails affirmatively.
(make-event (list 'defconst '*stcet-bad-row* (list 'quote (update-nth 3 "" *stcet-row*))))
(assert-event
 (with-guard-checking :none
  (and (not (or (fn-held-p *stcet-bad-row*) (fn-hstxa-p *stcet-bad-row*)))
       (not (equal (fn-stce-row-start-carried *stcet-bad-row*)
                   (fn-stce-row-start *stcet-bad-row*))))))
; Configuration lookup is an actual one-entry-per-resume phase. Its pinned
; source invariant is logical evidence, never a runtime whole-tail scan.
(defun fn-stcet-row-run (evidence cursor cfg generation keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (mv-let (e c v) (fn-stce-row-resume evidence cursor cfg generation keyring)
    (list e c v)))
(make-event
 (list 'defconst '*stcet-cfg*
       (list 'quote
        (fn-cfg-value-make
         (list (fn-cfg-group-make "other" 0 0 nil nil 1)
               (fn-cfg-group-make-with-authority
                "fn.test" 0 0 nil nil 1
                (fn-record-octets-string (fn-id-hex-octets *stcet-authority*)) 0))
         0 nil nil nil nil nil nil nil nil))))
(make-event
 (list 'defconst '*stcet-resolve*
       (list 'quote (fn-stce-authority-start
                     (fn-stce-row-start-carried *stcet-row*) *stcet-cfg* 0))))
(assert-event
 (and (consp (nth 2 (fn-stce-row-start-carried *stcet-row*)))
      (fn-stce-authority-sourcep *stcet-resolve*)))
(make-event
 (list 'defconst '*stcet-resolve-next*
       (list 'quote (nth 1 (fn-stcet-row-run nil *stcet-resolve* nil 9 *stcet-keyring*)))))
(assert-event
 (and (fn-stce-authority-tagp *stcet-resolve*)
      (consp (nth 1 *stcet-resolve*))
      (not (equal (fn-cfg-group-name (car (nth 1 *stcet-resolve*)))
                  (nth 2 *stcet-resolve*)))
      (equal (fn-stce-authority-sourcep *stcet-resolve-next*)
             (fn-stce-authority-sourcep *stcet-resolve*))
      (equal (nth 2 (fn-stcet-row-run nil *stcet-resolve* nil 9 *stcet-keyring*))
             :resolving-authority)))
(assert-event
 (and (fn-stce-authority-tagp *stcet-resolve-next*)
      (fn-stce-authority-sourcep *stcet-resolve-next*)
      (equal (fn-cfg-group-name (car (nth 1 *stcet-resolve-next*)))
             (nth 2 *stcet-resolve-next*))
      (equal (fn-stcet-row-run nil *stcet-resolve-next* nil 9 *stcet-keyring*)
             (fn-stcet-run nil (nth 4 *stcet-resolve-next*)
                           (fn-pta-group-authority *stcet-cfg* 0 "fn.test")
                           *stcet-keyring*))))
; Hypothesis removal, corrupted cursor: retain tag and terminal-tail premises,
; affirmatively falsify the pinned-source invariant and the exact result.
(make-event
 (list 'defconst '*stcet-resolve-bad*
       (list 'quote (update-nth 1 nil *stcet-resolve-next*))))
(assert-event
 (and (fn-stce-authority-tagp *stcet-resolve-bad*)
      (atom (nth 1 *stcet-resolve-bad*))
      (not (fn-stce-authority-sourcep *stcet-resolve-bad*))
      (not (equal (fn-stcet-row-run nil *stcet-resolve-bad* nil 9 *stcet-keyring*)
                  (fn-stcet-run nil (nth 4 *stcet-resolve-bad*)
                                (fn-pta-group-authority *stcet-cfg* 0 "fn.test")
                                *stcet-keyring*)))))
; Preservation hypothesis removals; each check retains all other premises.
(assert-event
 (and (fn-stce-authority-tagp *stcet-resolve-bad*)
      (not (consp (nth 1 *stcet-resolve-bad*)))
      (not (equal (fn-cfg-group-name (car (nth 1 *stcet-resolve-bad*)))
                  (nth 2 *stcet-resolve-bad*)))
      (not (equal (fn-stce-authority-sourcep
                   (nth 1 (fn-stcet-row-run nil *stcet-resolve-bad* nil 9 *stcet-keyring*)))
                  (fn-stce-authority-sourcep *stcet-resolve-bad*)))))
(make-event
 (list 'defconst '*stcet-resolve-wrong-cfg*
       (list 'quote (update-nth 5 nil *stcet-resolve-next*))))
(assert-event
 (and (fn-stce-authority-tagp *stcet-resolve-wrong-cfg*)
      (consp (nth 1 *stcet-resolve-wrong-cfg*))
      (equal (fn-cfg-group-name (car (nth 1 *stcet-resolve-wrong-cfg*)))
             (nth 2 *stcet-resolve-wrong-cfg*))
      (not (equal (fn-stce-authority-sourcep
                   (nth 1 (fn-stcet-row-run nil *stcet-resolve-wrong-cfg* nil 9 *stcet-keyring*)))
                  (fn-stce-authority-sourcep *stcet-resolve-wrong-cfg*)))))
; Terminal requirement removal: all source/tag premises hold, unresolved tail
; returns a further cursor rather than the exact completed core transition.
(assert-event
 (and (fn-stce-authority-tagp *stcet-resolve*)
      (fn-stce-authority-sourcep *stcet-resolve*)
      (not (or (atom (nth 1 *stcet-resolve*))
               (equal (fn-cfg-group-name (car (nth 1 *stcet-resolve*)))
                      (nth 2 *stcet-resolve*))))
      (not (equal (fn-stcet-row-run nil *stcet-resolve* nil 9 *stcet-keyring*)
                  (fn-stcet-run nil (nth 4 *stcet-resolve*)
                                (fn-pta-group-authority *stcet-cfg* 0 "fn.test")
                                *stcet-keyring*)))))

(make-event
 (list 'defconst '*stcet-resolve-wrong-tag*
       (list 'quote (update-nth 0 :bad
                      (update-nth 1 (list (car (nth 1 *stcet-resolve*))) *stcet-resolve*)))))
(assert-event
 (and (not (fn-stce-authority-tagp *stcet-resolve-wrong-tag*))
      (consp (nth 1 *stcet-resolve-wrong-tag*))
      (not (equal (fn-cfg-group-name (car (nth 1 *stcet-resolve-wrong-tag*)))
                  (nth 2 *stcet-resolve-wrong-tag*)))
      (not (equal (fn-stce-authority-sourcep
                   (nth 1 (fn-stcet-row-run nil *stcet-resolve-wrong-tag* nil 9 *stcet-keyring*)))
                  (fn-stce-authority-sourcep *stcet-resolve-wrong-tag*)))))
(make-event
 (list 'defconst '*stcet-terminal-wrong-tag*
       (list 'quote (update-nth 0 :bad *stcet-resolve-next*))))
(assert-event
 (and (not (fn-stce-authority-tagp *stcet-terminal-wrong-tag*))
      (fn-stce-authority-sourcep *stcet-terminal-wrong-tag*)
      (equal (fn-cfg-group-name (car (nth 1 *stcet-terminal-wrong-tag*)))
             (nth 2 *stcet-terminal-wrong-tag*))
      (not (equal (fn-stcet-row-run nil *stcet-terminal-wrong-tag* nil 9 *stcet-keyring*)
                  (fn-stcet-run nil (nth 4 *stcet-terminal-wrong-tag*)
                                (fn-pta-group-authority *stcet-cfg* 0 "fn.test")
                                *stcet-keyring*)))))
