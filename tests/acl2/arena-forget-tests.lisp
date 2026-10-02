; Teeth for the arena's forget (lane arena-forget, 2026-10-03):
;   PRF-1235 fn-arena-forget-payload        books/payload-arena.lisp
;   PRF-1235 fn-arx-forget-file-count       books/payload-arena-extent.lisp
;   PRF-1235 fn-arf-apply-released-payload  books/arena-forget.lisp
;   PRF-1235 fn-arf-changed-handles-are-unnamed
; and the composed runs: a reclaimed handle's forget takes its file's count
; to 0 (the file goes quiet); a holder still pinned keeps the forget pending
; (MUTATION: forget refused).

(in-package "ACL2")
(include-book "../../books/payload-arena-extent")
(include-book "../../books/payload-arena")
(include-book "../../books/arena-forget")
(include-book "../../books/arena-reader-pins")
(include-book "must-fail-checked")

(local (in-theory (enable (:definition fn-arn-extent-guardp))))

(assert-event
 (and (eq (symbol-class 'fn-arena$x-forget (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$l-forget (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arf-apply-released (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arf-apply-items (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arf-tag (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arf-retire-event (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arf-changed-handles (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; PRF-1235.  Positive, every conjunct with its antecedent at a ground arena.
(defthm arft-forget-positive
  (let* ((a '((1 2 3) (4 5) (6)))
         (a2 (fn-arena-forget 1 a)))
    (and (natp 1)
         (equal (fn-arena-payload 1 a2) nil)
         (natp 0) (not (equal 0 1))
         (equal (fn-arena-payload 0 a2) '(1 2 3))
         (equal (fn-arena-payload 2 a2) '(6))
         (equal (fn-arena-count a2) 3)
         (fn-arena-p a)
         (fn-arena-p a2)))
  :rule-classes nil)

; Without (natp h): h = -1 is no handle, the forget is the identity, and a
; read at -1 answers position 0's payload, not the empty one.
(defthm arft-forget-without-natp-h
  (and (not (natp -1))
       (equal (fn-arena-payload -1 (fn-arena-forget -1 '((1 2 3) (4 5)))) '(1 2 3)))
  :rule-classes nil)

(local
 (must-fail-checked
  (defthm arft-forget-keystone-without-natp-h
    (equal (fn-arena-payload h (fn-arena-forget h fn-arena)) nil))))

; Without (natp k): k = -1 differs from h = 0 and reads the position the
; forget emptied.
(defthm arft-forget-without-natp-k
  (and (not (natp -1)) (not (equal -1 0))
       (equal (fn-arena-payload -1 (fn-arena-forget 0 '((1 2 3) (4 5)))) nil)
       (equal (fn-arena-payload -1 '((1 2 3) (4 5))) '(1 2 3)))
  :rule-classes nil)

(local
 (must-fail-checked
  (defthm arft-forget-keystone-without-natp-k
    (implies (not (equal k h))
             (equal (fn-arena-payload k (fn-arena-forget h fn-arena))
                    (fn-arena-payload k fn-arena))))))

; Without (not (equal k h)): the forgotten handle itself.
(local
 (must-fail-checked
  (defthm arft-forget-keystone-without-distinct
    (implies (natp k)
             (equal (fn-arena-payload k (fn-arena-forget h fn-arena))
                    (fn-arena-payload k fn-arena))))))

; Without (fn-arena-p fn-arena): a value that is no arena stays none.
(defthm arft-forget-without-arena-p
  (and (not (fn-arena-p '((1 2 3) . 7)))
       (not (fn-arena-p (fn-arena-forget 0 '((1 2 3) . 7)))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The concrete run (books/payload-arena-extent.lisp).  Handle 0 an extent on
; file 7, handle 1 resident, handle 2 an extent on file 7, handle 3 staged.
; Forget 0: file 7's count 2 -> 1, still named.  Forget 2: 1 -> 0, the file
; is unnamed (what fn-xrt-quiet-files reads).  Forget 3 (staged) and 1
; (resident): both read empty, through no realizer.  A forget outside the
; arena changes nothing.  A seal after the forgets takes handle 4: no handle
; is reused.
(defun arft-run (fn-octets fn-arena-extent)
  ; guards unverified: each export checks its own guard when the run executes
  (declare (xargs :stobjs (fn-octets fn-arena-extent) :verify-guards nil))
  (let* ((fn-octets (fn-octets-clear fn-octets))
         (fn-octets (fn-octets-append-list '(1 2 3 4) fn-octets))
         (fn-arena-extent (fn-arena-extent-clear fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-seal-extent 7 100 100 120 20 99 fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-seal-list '(9 9) fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-seal-extent 7 300 100 320 30 98 fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-seal-buffer fn-octets fn-arena-extent))
         (before (list (fn-arena-extent-payload-len 0 fn-arena-extent)
                       (fn-arena-extent-payload 3 fn-arena-extent)))
         (fn-arena-extent (fn-arena-extent-forget 0 fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-forget 2 fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-forget 3 fn-arena-extent))
         (mid (list (fn-arena-extent-payload 1 fn-arena-extent)))
         (fn-arena-extent (fn-arena-extent-forget 1 fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-forget 17 fn-arena-extent))
         (fn-arena-extent (fn-arena-extent-seal-list '(5) fn-arena-extent)))
    (mv (list before mid
              (fn-arena-extent-count fn-arena-extent)
              (fn-arena-extent-payload-len 0 fn-arena-extent)
              (fn-arena-extent-payload 0 fn-arena-extent)
              (fn-arena-extent-payload 1 fn-arena-extent)
              (fn-arena-extent-payload 2 fn-arena-extent)
              (fn-arena-extent-payload 3 fn-arena-extent)
              (fn-arena-extent-payload 4 fn-arena-extent))
        fn-octets fn-arena-extent)))

(assert-event (mv-let (r fn-octets fn-arena-extent) (arft-run fn-octets fn-arena-extent)
                (mv (equal r '((20 (1 2 3 4)) ((9 9)) 5 0 nil nil nil nil (5)))
                    fn-octets fn-arena-extent))
              :stobjs-out '(nil fn-octets fn-arena-extent))

; The file count through the forgets.
(defun arft-files-run (fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :verify-guards nil))
  (let* ((fn-arena$x (fn-arena$x-clear fn-arena$x))
         (fn-arena$x (fn-arena$x-seal-extent 7 100 100 120 20 99 fn-arena$x))
         (fn-arena$x (fn-arena$x-seal-list '(9 9) fn-arena$x))
         (fn-arena$x (fn-arena$x-seal-extent 7 300 100 320 30 98 fn-arena$x))
         (c0 (fn-arx-file-count 7 fn-arena$x))
         (fn-arena$x (fn-arena$x-forget 0 fn-arena$x))
         (c1 (fn-arx-file-count 7 fn-arena$x))
         (u1 (fn-arx-files-unnamed-p '(7) fn-arena$x))
         (fn-arena$x (fn-arena$x-forget 2 fn-arena$x)))
    (mv (list c0 c1 u1
              (fn-arx-file-count 7 fn-arena$x)
              (fn-arx-files-unnamed-p '(7) fn-arena$x)
              (fn-arena$x-exti 0 fn-arena$x)
              (fn-arena$x-exti 2 fn-arena$x))
        fn-arena$x)))

(defun arft-files-run-result ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena$x
    (mv-let (r fn-arena$x) (arft-files-run fn-arena$x) r)))

(assert-event (equal (arft-files-run-result) '(2 1 nil 0 t :forgotten :forgotten)))

; -----------------------------------------------------------------------------
; PRF-1235.  A reached state: the extent on file 7 at handle 0, a resident
; handle 1.
(defun-nx arft-x2 ()
  (fn-arena$x-seal-list '(1 2)
    (fn-arena$x-seal-extent 7 100 100 120 20 99
      (fn-arena$x-clear (create-fn-arena$x)))))

(defun arft-a2 ()
  (fn-arena$a-seal-list '(1 2)
    (fn-arena$a-seal-extent 7 100 100 120 20 99
      (fn-arena$a-clear (create-fn-arena$a)))))

(defthm arft-x2-corresponds
  (fn-arena$xcorr (arft-x2) (arft-a2))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable fn-arena$xcorr fn-arena$x-clear fn-arena$x-seal-extent
                               fn-arena$x-seal-list create-fn-arena$x
                               (:e fn-arena$x-clear) (:e fn-arena$x-seal-extent)
                               (:e fn-arena$x-seal-list) (:e create-fn-arena$x))
           :use ((:instance create-fn-arena-extent{correspondence})
                 (:instance fn-arena-extent-clear{correspondence}
                            (fn-arena$x (create-fn-arena$x)) (fn-arena-extent (create-fn-arena$a)))
                 (:instance fn-arena-extent-seal-extent{correspondence}
                            (file 7) (eoff 100) (elen 100) (poff 120) (plen 20) (trailer 99)
                            (fn-arena$x (fn-arena$x-clear (create-fn-arena$x)))
                            (fn-arena-extent (fn-arena$a-clear (create-fn-arena$a))))
                 (:instance fn-arena-extent-seal-list{correspondence} (xs '(1 2))
                            (fn-arena$x (fn-arena$x-seal-extent 7 100 100 120 20 99
                                          (fn-arena$x-clear (create-fn-arena$x))))
                            (fn-arena-extent (fn-arena$a-seal-extent 7 100 100 120 20 99
                                               (fn-arena$a-clear (create-fn-arena$a)))))))))

; Positive: the complete antecedent and both arms of the conclusion (the
; named file 7 loses one; file 9, not named by handle 0, keeps its count).
(defthm arft-file-count-positive
  (and (fn-arena$xcorr (arft-x2) (arft-a2))
       (natp 0) (< 0 (len (arft-a2))) (natp 7) (natp 9)
       (equal (fn-arx-entry-file (nth 0 (nth *fn-arena$x-exti* (arft-x2)))) 7)
       (equal (fn-arx-file-count 7 (arft-x2)) 1)
       (equal (fn-arx-file-count 7 (fn-arena$x-forget 0 (arft-x2))) 0)
       (equal (fn-arx-file-count 9 (fn-arena$x-forget 0 (arft-x2)))
              (fn-arx-file-count 9 (arft-x2))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance arft-x2-corresponds))
           :in-theory (e/d (fn-arena$x-forget fn-arx-entry-file) (fn-arena$xcorr)))))

; Without the correspondence (CORRUPTED-STATE witness): an extent column
; naming file 7 at handle 0 beside an empty count column.  The forget cannot
; take the count below 0.
(defthm arft-file-count-without-corr-corrupted-state
  (let ((x (list '(nil) '((7 100 100 120 20 99)) nil nil)))
    (and (not (fn-arx-files-agree (nth *fn-arena$x-exti* x) (nth *fn-arena$x-filesi* x)))
         (not (fn-arena$xcorr x a))
         (natp 0) (natp 7)
         (equal (fn-arx-entry-file (nth 0 (nth *fn-arena$x-exti* x))) 7)
         (equal (fn-arx-file-count 7 x) 0)
         (equal (fn-arx-file-count 7 (fn-arena$x-forget 0 x)) 0)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arx-files-agree-necc (f 7)
                                   (ext '((7 100 100 120 20 99))) (files nil)))
           :in-theory (e/d (fn-arx-files-get fn-arx-entry-file fn-arena$x-forget fn-arx-mark
                            fn-arx-files-move)
                           (fn-arx-files-agree-necc)))))

(local
 (must-fail-checked
  (defthm arft-file-count-keystone-without-corr
    (implies (and (natp h) (< h (len fn-arena$a)) (natp f))
             (equal (fn-arx-file-count f (fn-arena$x-forget h fn-arena$x))
                    (- (fn-arx-file-count f fn-arena$x)
                       (if (equal (fn-arx-entry-file (nth h (nth *fn-arena$x-exti* fn-arena$x))) f)
                           1
                         0)))))))

; Without (natp f): f = NIL is no file id; the resident handle 1 names no
; file (NIL), so the right side subtracts one from column 0's count while the
; forget moves nothing.
(defthm arft-file-count-without-natp-f
  (and (fn-arena$xcorr (arft-x2) (arft-a2))
       (natp 1) (< 1 (len (arft-a2)))
       (not (natp nil))
       (equal (fn-arx-entry-file (nth 1 (nth *fn-arena$x-exti* (arft-x2)))) nil)
       (equal (fn-arx-file-count nil (fn-arena$x-forget 1 (arft-x2)))
              (fn-arx-file-count nil (arft-x2))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance arft-x2-corresponds))
           :in-theory (e/d (fn-arena$x-forget fn-arx-entry-file) (fn-arena$xcorr)))))

(local
 (must-fail-checked
  (defthm arft-file-count-keystone-without-natp-f
    (implies (and (fn-arena$xcorr fn-arena$x fn-arena$a)
                  (natp h) (< h (len fn-arena$a)))
             (equal (fn-arx-file-count f (fn-arena$x-forget h fn-arena$x))
                    (- (fn-arx-file-count f fn-arena$x)
                       (if (equal (fn-arx-entry-file (nth h (nth *fn-arena$x-exti* fn-arena$x))) f)
                           1
                         0)))))))

; Without (< h (len a)): handle 5 is outside the arena, the forget is the
; identity; the statement would still subtract for an entry past the count.
(local
 (must-fail-checked
  (defthm arft-file-count-keystone-without-in-arena
    (implies (and (fn-arena$xcorr fn-arena$x fn-arena$a)
                  (natp h) (natp f))
             (equal (fn-arx-file-count f (fn-arena$x-forget h fn-arena$x))
                    (- (fn-arx-file-count f fn-arena$x)
                       (if (equal (fn-arx-entry-file (nth h (nth *fn-arena$x-exti* fn-arena$x))) f)
                           1
                         0)))))))

(local
 (must-fail-checked
  (defthm arft-file-count-keystone-without-natp-h
    (implies (and (fn-arena$xcorr fn-arena$x fn-arena$a)
                  (< h (len fn-arena$a)) (natp f))
             (equal (fn-arx-file-count f (fn-arena$x-forget h fn-arena$x))
                    (- (fn-arx-file-count f fn-arena$x)
                       (if (equal (fn-arx-entry-file (nth h (nth *fn-arena$x-exti* fn-arena$x))) f)
                           1
                         0)))))))

; -----------------------------------------------------------------------------
; PRF-1235 over the pins step (books/arena-reader-pins.lisp), the host's
; sequence.  A reader pins generation 0; the swap retires handle 1 (stamp 0);
; a staged page's handle 2 is retired (stamp 1).

(defun arft-step (st ev)
  (declare (xargs :guard (fn-arpn-okp st)))
  (mv-list 2 (fn-arpn-step st ev)))

(defconst *arft-st1*
  (first (arft-step (first (arft-step (first (arft-step (fn-arpn-initial) '(:pin)))
                                      (fn-arf-retire-event '(1))))
                    '(:retire (2)))))

(assert-event (equal *arft-st1* '(2 ((0 . 1)) ((1 2) (0 (:forget 1))))))

; MUTATION (a holder is still live: the forget is refused).  The reader
; pinned at 0 runs: the release answers nothing, handle 1 keeps its payload.
(defthm arft-live-holder-keeps-the-payload
  (let ((rel (second (arft-step *arft-st1* '(:release)))))
    (and (equal rel nil)
         (equal (fn-arf-apply-released rel '((1 2 3) (4 5) (6))) '((1 2 3) (4 5) (6)))
         (equal (third (first (arft-step *arft-st1* '(:release))))
                '((1 2) (0 (:forget 1))))))
  :rule-classes nil)

; Positive: the reader ends; the release answers both retirements; the
; tagged handle 1 is emptied, the staged page's handle 2 (a release, no
; forget) and handle 0 keep their payloads, the count is 3.
(defconst *arft-st2* (first (arft-step *arft-st1* '(:unpin 0))))
(defconst *arft-rel* (second (arft-step *arft-st2* '(:release))))

(defthm arft-apply-released-positive
  (let ((a2 (fn-arf-apply-released *arft-rel* '((1 2 3) (4 5) (6)))))
    (and (equal *arft-rel* '((1 2) (0 (:forget 1))))
         (equal (fn-arf-pend-handles *arft-rel*) '(1))
         (natp 1) (member-equal 1 (fn-arf-pend-handles *arft-rel*))
         (equal (fn-arena-payload 1 a2) nil)
         (natp 2) (not (member-equal 2 (fn-arf-pend-handles *arft-rel*)))
         (equal (fn-arena-payload 2 a2) '(6))
         (equal (fn-arena-payload 0 a2) '(1 2 3))
         (equal (fn-arena-count a2) 3)
         (fn-arena-p '((1 2 3) (4 5) (6)))
         (fn-arena-p a2)))
  :rule-classes nil)

; Without (natp k): k = -1 is not among the handles and reads position 0,
; which a forget of handle 0 empties.
(defthm arft-apply-released-without-natp-k
  (and (not (natp -1))
       (not (member-equal -1 (fn-arf-pend-handles '((0 (:forget 0))))))
       (equal (fn-arena-payload -1 (fn-arf-apply-released '((0 (:forget 0))) '((1 2 3) (4 5))))
              nil)
       (equal (fn-arena-payload -1 '((1 2 3) (4 5))) '(1 2 3)))
  :rule-classes nil)

(local
 (must-fail-checked
  (defthm arft-apply-released-keystone-without-natp-k
    (implies (not (member-equal k (fn-arf-pend-handles rel)))
             (equal (fn-arena-payload k (fn-arf-apply-released rel fn-arena))
                    (fn-arena-payload k fn-arena))))))

; Without the membership test: a handle that is not released keeps its payload.
(local
 (must-fail-checked
  (defthm arft-apply-released-keystone-without-member
    (implies (natp k)
             (equal (fn-arena-payload k (fn-arf-apply-released rel fn-arena))
                    nil)))))

; -----------------------------------------------------------------------------
; PRF-1235.  Three held rows at handles 0, 1, 2; the rewrite replaces the
; middle one by a row at the fresh handle 3.

(defconst *arft-w*
  (fn-record-make 0 1 0 "<a@x>" '(83 58 32 97 13 10 13 10) '("fn.test") "o" "s" "e" 1 5))

(defconst *arft-old*
  (list (fn-held-plain *arft-w* 0) (fn-held-plain *arft-w* 1) (fn-held-plain *arft-w* 2)))
(defconst *arft-new*
  (list (fn-held-plain *arft-w* 0) (fn-held-plain *arft-w* 3) (fn-held-plain *arft-w* 2)))

(defthm arft-changed-positive
  (and (equal (fn-arf-rows-handles *arft-old*) '(0 1 2))
       (no-duplicatesp-equal (fn-arf-rows-handles *arft-old*))
       (fn-arf-rewrite-of-p *arft-old* *arft-new* (fn-arf-rows-handles *arft-old*))
       (equal (fn-arf-changed-handles *arft-old* *arft-new*) '(1))
       (equal (fn-arf-rows-handles *arft-new*) '(0 3 2))
       (fn-arf-disjointp (fn-arf-changed-handles *arft-old* *arft-new*)
                         (fn-arf-rows-handles *arft-new*)))
  :rule-classes nil)

; Without distinct old handles: two old rows name handle 1; the rewrite
; changes the first and keeps the second, which still names it.
(defconst *arft-old-dup*
  (list (fn-held-plain *arft-w* 1) (fn-held-plain *arft-w* 1)))
(defconst *arft-new-dup*
  (list (fn-held-plain *arft-w* 3) (fn-held-plain *arft-w* 1)))

(defthm arft-changed-without-distinct
  (and (not (no-duplicatesp-equal (fn-arf-rows-handles *arft-old-dup*)))
       (fn-arf-rewrite-of-p *arft-old-dup* *arft-new-dup* (fn-arf-rows-handles *arft-old-dup*))
       (equal (fn-arf-changed-handles *arft-old-dup* *arft-new-dup*) '(1))
       (not (fn-arf-disjointp (fn-arf-changed-handles *arft-old-dup* *arft-new-dup*)
                              (fn-arf-rows-handles *arft-new-dup*))))
  :rule-classes nil)

(local
 (must-fail-checked
  (defthm arft-changed-keystone-without-distinct
    (implies (fn-arf-rewrite-of-p old new (fn-arf-rows-handles old))
             (fn-arf-disjointp (fn-arf-changed-handles old new)
                               (fn-arf-rows-handles new))))))

; Without the rewrite relation: the changed positions swap two old handles
; (no fresh handle), so each retired handle is still named.
(defconst *arft-new-swap*
  (list (fn-held-plain *arft-w* 1) (fn-held-plain *arft-w* 0) (fn-held-plain *arft-w* 2)))

(defthm arft-changed-without-rewrite
  (and (no-duplicatesp-equal (fn-arf-rows-handles *arft-old*))
       (not (fn-arf-rewrite-of-p *arft-old* *arft-new-swap* (fn-arf-rows-handles *arft-old*)))
       (equal (fn-arf-changed-handles *arft-old* *arft-new-swap*) '(0 1))
       (not (fn-arf-disjointp (fn-arf-changed-handles *arft-old* *arft-new-swap*)
                              (fn-arf-rows-handles *arft-new-swap*))))
  :rule-classes nil)

(local
 (must-fail-checked
  (defthm arft-changed-keystone-without-rewrite
    (implies (no-duplicatesp-equal (fn-arf-rows-handles old))
             (fn-arf-disjointp (fn-arf-changed-handles old new)
                               (fn-arf-rows-handles new))))))
