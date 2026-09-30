; Literal teeth for unchanged fn-scr-source-scan-span-is-scan-of-consumed-prefix.
; No hypotheses to remove. Real octet/arena/catalog stobjs and an opened reader.
; Pure scanner correspondence only: offered-source custody/funding stays outer.
(in-package "ACL2")
(include-book "../../books/served-catalog-chain")
(defun ssct-line (s) (append (fn-nntp-string-octets s) '(13 10)))
(defconst *ssct-groups* '("fn.test"))
(defconst *ssct-config*
 (fn-inj-make-config t (fn-nntp-string-octets "fn.example.invalid")
   (list (fn-nntp-string-octets "fn.test")) 32768))
(defconst *ssct-observation* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *ssct-reader*
 (fn-served-result-conn
  (fn-served-open (fn-initial-state *ssct-groups*) 510 8192 *ssct-config*
   *ssct-observation* *ssct-observation* (fn-auth-open-config))))
(assert-event (and (fn-served-connp *ssct-reader*)
                  (fn-wire-fast-statep (fn-served-conn-wire *ssct-reader*))))
(assert-event
 (equal (list (symbol-class 'fn-scr-source-scan-span (w state))
              (symbol-class 'fn-scr-source-prepare-span (w state))
              (symbol-class 'fn-scr-source-boundary-dispatch (w state)))
        (make-list 3 :initial-element :common-lisp-compliant)))
(defun ssct-prefix (conn i end fn-octets fn-arena fn-cat)
 (declare (xargs :stobjs (fn-octets fn-arena fn-cat) :verify-guards nil))
 (let ((r (fn-scr-source-scan-span conn i end nil nil nil nil nil fn-octets fn-arena fn-cat)))
  (equal r (fn-scr-scan-span conn i (+ i (fn-served-counted-consumed r))
                           nil nil nil nil nil fn-octets fn-arena fn-cat))))
(defun ssct-mixed (command fn-octets fn-arena fn-cat)
 (declare (xargs :stobjs (fn-octets fn-arena fn-cat) :verify-guards nil))
 (let* ((bytes (append (ssct-line "OVER") (ssct-line command) (ssct-line "OVER")))
        (fn-octets (fn-octets-from-list bytes fn-octets))
        (end (fn-octets-len fn-octets))
        (p0 (fn-scr-source-prepare-span *ssct-reader* 0 end nil nil nil nil nil
                                      fn-octets fn-arena fn-cat))
        (r0 (nth 1 p0))
        (n0 (fn-served-counted-consumed r0))
        (c0 (fn-served-result-conn (fn-served-counted-result r0)))
        (p1 (fn-scr-source-prepare-span c0 n0 end nil nil nil nil nil
                                      fn-octets fn-arena fn-cat)))
  (mv-let (word r1)
   (fn-scr-source-boundary-dispatch p1 nil nil nil nil nil fn-arena fn-cat)
   (let* ((n1 (fn-served-counted-consumed r1))
          (c1 (fn-served-result-conn (fn-served-counted-result r1)))
          (p2 (fn-scr-source-prepare-span c1 (+ n0 n1) end nil nil nil nil nil
                                        fn-octets fn-arena fn-cat))
          (r2 (nth 1 p2))
          (whole (fn-scr-scan-span *ssct-reader* 0 end nil nil nil nil nil
                                   fn-octets fn-arena fn-cat)))
    (mv
     (and (eq (car p0) :source-result)
          (equal n0 (len (ssct-line "OVER")))
          (equal r0 (fn-scr-scan-span *ssct-reader* 0 n0 nil nil nil nil nil
                                     fn-octets fn-arena fn-cat))
          (eq (car p1) :source-boundary) (equal (nth 2 p1) n0)
          (eq word :dispatched) (equal n1 (len (ssct-line command)))
          (equal r1 (fn-scr-scan-span c0 n0 (+ n0 n1) nil nil nil nil nil
                                     fn-octets fn-arena fn-cat))
          (eq (car p2) :source-result)
          (equal (+ n0 n1 (fn-served-counted-consumed r2)) end)
          (equal (fn-served-result-conn (fn-served-counted-result r2))
                 (fn-served-result-conn (fn-served-counted-result whole)))
          (equal (append (fn-served-result-effects (fn-served-counted-result r0))
                         (fn-served-result-effects (fn-served-counted-result r1))
                         (fn-served-result-effects (fn-served-counted-result r2)))
                 (fn-served-result-effects (fn-served-counted-result whole)))
          (ssct-prefix *ssct-reader* 0 end fn-octets fn-arena fn-cat)
          (ssct-prefix c0 n0 end fn-octets fn-arena fn-cat)
          (ssct-prefix c1 (+ n0 n1) end fn-octets fn-arena fn-cat)
          (ssct-prefix *ssct-reader* 0 0 fn-octets fn-arena fn-cat)
          (ssct-prefix *ssct-reader* 0 3 fn-octets fn-arena fn-cat))
     fn-octets)))))
(defun ssct-run (command)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-octets
  (mv-let (v fn-octets)
   (with-local-stobj fn-arena
    (mv-let (v fn-octets fn-arena)
     (with-local-stobj fn-cat
      (mv-let (v fn-octets fn-cat)
       (mv-let (v fn-octets) (ssct-mixed command fn-octets fn-arena fn-cat)
        (mv v fn-octets fn-cat))
       (mv v fn-octets fn-arena)))
     (mv v fn-octets))) v)))
; Reachable positive full literal theorem and prefix/remainder path.
(assert-event (ssct-run "GROUP fn.test"))
(assert-event (ssct-run "LISTGROUP fn.test"))
