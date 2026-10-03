; Incremental construction of the existing P3 history image. The native
; publisher calls one row step at a time under its captured-image custody.
; A consumed suffix slot is cleared, so an image build never retains a
; second array of every event. Pages and commit plan remain the existing
; FNADTSN2 representation; this is not another history store.
(in-package "ACL2")
(include-book "history-records")

; Cooperative scheduling cadence of the publisher's existing row loop.
; This does not bound the page codec's relocation or a record's byte size.
(defconst *fn-his-build-yield-rows* 256)
(defun fn-his-build-yieldp (ordinal)
  (declare (xargs :guard (natp ordinal)))
  (equal (mod ordinal *fn-his-build-yield-rows*) 0))

(defun fn-his-build-begin (salt fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :guard (natp salt)))
  (let ((fn-hrecs$c (fn-hrc-reset salt fn-hrecs$c)))
    (resize-fn-hrc-sfx 0 fn-hrecs$c)))

(defthm fn-his-build-begin-establishes
  (implies (natp salt)
           (let ((c (fn-his-build-begin salt fn-hrecs$c)))
             (and (fn-hrc-wfp c) (fn-hrs-rel nil c)
                  (equal (fn-hrc-lo c) 0) (equal (fn-hrc-hi c) 0)
                  (equal (fn-hrc-sfx-length c) 0))))
  :hints (("Goal" :in-theory (enable fn-hrc-wfp fn-hrs-rel
                                    fn-hrc-reset fn-hrs-img-ok fn-hrc-fields fn-hrc-updaters))))

; Only a completely drained one-row suffix may be recycled. A refused
; flush preserves its pending row for diagnosis/recovery; it is not lost.
(defun fn-his-build-recycle (fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :guard (fn-hrc-wfp fn-hrecs$c)))
  (if (not (and (equal (fn-hrc-lo fn-hrecs$c) 1)
                (equal (fn-hrc-hi fn-hrecs$c) 1)))
      fn-hrecs$c
    (let* ((fn-hrecs$c (update-fn-hrc-sfxi 0 nil fn-hrecs$c))
           (fn-hrecs$c (update-fn-hrc-lo 0 fn-hrecs$c)))
      (update-fn-hrc-hi 0 fn-hrecs$c))))

(defthm fn-his-build-recycle-keeps-history
  (implies (and (fn-hrc-wfp c) (fn-hrs-rel h c))
           (and (fn-hrc-wfp (fn-his-build-recycle c))
                (fn-hrs-rel h (fn-his-build-recycle c))))
  :hints (("Goal" :in-theory (enable fn-his-build-recycle fn-hrc-wfp
                                    fn-hrs-rel fn-hrc-sfx-list))))

(defun fn-his-build-row (ev fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :guard (fn-hrc-wfp fn-hrecs$c)
                  :guard-hints (("Goal" :in-theory
                    (disable fn-hrc-wfp fn-hrc-append fn-hrc-flush-one
                             fn-his-build-recycle)))))
  (if (not (and (equal (fn-hrc-lo fn-hrecs$c) 0)
                (equal (fn-hrc-hi fn-hrecs$c) 0)))
      (mv (list :refused :pending-suffix) fn-hrecs$c)
    (let ((fn-hrecs$c (fn-hrc-append ev fn-hrecs$c)))
      (mv-let (v fn-hrecs$c) (fn-hrc-flush-one fn-hrecs$c)
        (let ((fn-hrecs$c (fn-his-build-recycle fn-hrecs$c)))
          (mv v fn-hrecs$c))))))

(defthm fn-his-build-row-bounds-suffix-capacity
  (implies (<= (fn-hrc-sfx-length c) 16)
           (<= (fn-hrc-sfx-length (mv-nth 1 (fn-his-build-row ev c))) 16))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-his-build-row fn-his-build-recycle
                            fn-hrc-append fn-hrc-flush-one fn-hrc-flush-init
                            fn-hrc-flush-step)
                           (fn-hp-x-init fn-hp-x-append-step)))))

; PRF-1265. This is the subject the native publication calls. It appends
; every event type to the image's history, keeps representation faithfulness
; even when flushing refuses, and refuses a pending suffix without effects.
(defthm fn-his-build-row-refines-history-append
  (implies (and (fn-hrc-wfp c) (fn-hrs-rel h c))
           (let ((next (mv-nth 1 (fn-his-build-row ev c))))
             (and (fn-hrc-wfp next)
                  (if (and (equal (fn-hrc-lo c) 0) (equal (fn-hrc-hi c) 0))
                      (fn-hrs-rel (append h (list ev)) next)
                    (and (equal (mv-nth 0 (fn-his-build-row ev c))
                                '(:refused :pending-suffix))
                         (equal next c))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrc-append-rel (fn-hrecs$c c))
                 (:instance fn-hrc-flush-one-rel
                            (fn-hrecs$c (fn-hrc-append ev c))
                            (h (append h (list ev))))
                 (:instance fn-his-build-recycle-keeps-history
                            (c (mv-nth 1 (fn-hrc-flush-one (fn-hrc-append ev c))))
                            (h (append h (list ev)))))
           :in-theory (e/d (fn-his-build-row)
                           (fn-hrc-wfp fn-hrs-rel fn-hrc-append
                            fn-hrc-flush-one fn-his-build-recycle)))))
