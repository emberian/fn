; fn: the record view over the image and the in-memory suffix (lane
; arena-store-4, 2026-09-28, m3c P1).  Prefix fn-hp-.
;
; KEYSTONE fn-hp-records-at-is-nth: `fn-hp-records-at' answers record I of
; the history the image holds (length N) followed by an in-memory SUFFIX:
; an :ok answer is the I-th element of (append H SUFFIX), below the end
; the verdict is :ok or a need-verdict (`fn-hp-need-verdictp'), past the
; end (:refused :seq).  SUFFIX is any true list of events.
;
; The store's records (books/store-files.lisp `fn-sf-records', the
; snoc-list `fn-sf-records-field' read oldest first) are, once the image
; exists, the image's history H followed by the records appended since
; the image's last append: the host passes that tail as SUFFIX.  That
; link -- (fn-sf-records s) = (append H SUFFIX) for the store the host
; keeps -- is not proved here; it is the owner wiring's obligation.
(in-package "ACL2")
(include-book "history-pages-placed")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable floor mod pgs-true-list-fix-when-true-listp pgs-ptab-p-true-listp fn-cp-id-length-bound
                           fn-scc-encode-is-program)))

(defun fn-hp-need-verdictp (v)
  ; a verdict the host serves before it asks again: a table or page to
  ; fill, or :out-of-range
  (declare (xargs :guard t))
  (or (eq v :out-of-range)
      (and (consp v) (or (eq (car v) :need-table) (eq (car v) :need-page)))))

(defthm fn-hp-x-ready-verdict
  (implies (not (equal (fn-hp-x-ready p pgs-mem) :ok)) (fn-hp-need-verdictp (fn-hp-x-ready p pgs-mem))))

(defthm fn-hp-x-ready-range-verdict
  (implies (not (equal (fn-hp-x-ready-range p hi pgs-mem) :ok))
           (fn-hp-need-verdictp (fn-hp-x-ready-range p hi pgs-mem)))
  :hints (("Goal" :induct (fn-hp-x-ready-range p hi pgs-mem) :in-theory (disable fn-hp-x-ready fn-hp-need-verdictp))))

(defthm fn-hp-x-cell-verdict
  (implies (not (equal (car (fn-hp-x-cell r seq starts pgs-mem)) :ok))
           (fn-hp-need-verdictp (car (fn-hp-x-cell r seq starts pgs-mem))))
  :hints (("Goal" :in-theory (disable fn-hp-x-ready fn-hp-need-verdictp))))

(defthm fn-hp-x-pool-ready-verdict
  (implies (not (equal (fn-hp-x-pool-ready lo k pgs-mem) :ok))
           (fn-hp-need-verdictp (fn-hp-x-pool-ready lo k pgs-mem)))
  :hints (("Goal" :in-theory (disable fn-hp-x-ready-range fn-hp-need-verdictp))))

(defthm fn-hp-x-at-verdict
  (implies (not (equal (mv-nth 0 (fn-hp-x-at seq salt n lens starts pgs-mem)) :ok))
           (fn-hp-need-verdictp (mv-nth 0 (fn-hp-x-at seq salt n lens starts pgs-mem))))
  :hints (("Goal" :in-theory (disable fn-hp-x-ready fn-hp-x-ready-range fn-hp-need-verdictp fn-hp-at-core fn-hp-x-words
                                      fn-hp-pool-lo fn-hp-x-cell fn-hp-x-pool-ready mod floor mod-=-0 nfix))))

(defun fn-hp-records-at (i n suffix salt lens starts pgs-mem)
  ; Record I of the history the image holds followed by SUFFIX, as the
  ; host calls it: (mv VERDICT RESULT).  I < N: the image's row I
  ; (`fn-hp-x-at'); a need-verdict is what the host serves before it asks
  ; again.  Otherwise the in-memory SUFFIX's element I - N, or (:refused
  ; :seq) past its end.  N LENS STARTS: the image's header answer.  Work:
  ; the row read, or I - N steps down SUFFIX.  Changes nothing.
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp i) (natp n) (true-listp suffix) (true-listp lens) (fn-hp-starts-okp starts))))
  (if (< i n)
      (fn-hp-x-at i salt n lens starts pgs-mem)
    (let ((tl (nthcdr (- i n) suffix)))
      (if (consp tl)
          (mv :ok (list :ok (car tl)))
        (mv :ok (list :refused :seq))))))

(local
 (defthm fn-hp-nth-append-v
   (implies (natp i)
            (equal (nth i (append a b)) (if (< i (len a)) (nth i a) (nth (- i (len a)) b))))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-hp-consp-nthcdr-v
   (implies (natp j) (iff (consp (nthcdr j l)) (< j (len l))))
   :hints (("Goal" :induct (nthcdr j l) :in-theory (enable nthcdr)))))

(local
 (defthm fn-hp-car-nthcdr-v
   (implies (natp j) (equal (car (nthcdr j l)) (nth j l)))
   :hints (("Goal" :induct (nthcdr j l) :in-theory (enable nth nthcdr)))))

; KEYSTONE (the record view): over any page store state whose verified
; pages hold the history H's image placed at STARTS in NP pages, with N
; its length, record I of H followed by SUFFIX: an answer (:ok (:ok X))
; has X the I-th element of (append H SUFFIX); below the end the verdict
; is :ok or a need-verdict; past the end the answer is (:refused :seq).
(defthm fn-hp-records-at-is-nth
  (implies (and (fn-hp-okp h salt) (equal n (len h)) (equal lens (fn-hp-lens h salt))
                (fn-hp-starts-okp starts) (adt-placement-ok starts lens np)
                (fn-hp-vhold 0 (pgs-v-length pgs-mem) pgs-mem (fn-hp-piw h salt starts np))
                (natp i))
           (let ((res (fn-hp-records-at i n suffix salt lens starts pgs-mem)))
             (and (implies (and (< i (+ n (len suffix))) (equal (mv-nth 0 res) :ok))
                           (equal (mv-nth 1 res) (list :ok (nth i (append h suffix)))))
                  (implies (< i (+ n (len suffix)))
                           (or (equal (mv-nth 0 res) :ok) (fn-hp-need-verdictp (mv-nth 0 res))))
                  (implies (not (< i (+ n (len suffix))))
                           (and (equal (mv-nth 0 res) :ok) (equal (mv-nth 1 res) '(:refused :seq)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hp-x-at-is-nth-placed (seq i))
                 (:instance fn-hp-x-at-verdict (seq i) (n (len h)) (lens (fn-hp-lens h salt))))
           :in-theory (disable fn-hp-x-at-is-nth-placed fn-hp-x-at-verdict fn-hp-x-at fn-hp-need-verdictp
                               fn-hp-okp fn-hp-lens fn-hp-piw fn-hp-vhold adt-placement-ok nthcdr))))
