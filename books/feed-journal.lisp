; FNFD physical envelope and bounded recovery decisions. The host reads at
; most four prefix octets and then the frame length this book authorizes.
; Partial final envelopes are repairable; complete invalid evidence is not.
(in-package "ACL2")
(include-book "peer-feed")
(include-book "frame-trailer")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (enable fn-frame-octet-vocabulary)))

(defconst *fn-feed-journal-prefix-size* 4)
(defconst *fn-feed-journal-frame-min*
  (+ *fn-frame-header-octets* *fn-frame-trailer-octets*))
(defconst *fn-feed-journal-frame-max*
  (+ *fn-feed-journal-frame-min* *fn-feed-max-payload*))

(defun fn-feed-journal-prefix (prefix)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((not (fn-cbor-octet-listp prefix)) :invalid)
        ((equal (len prefix) 0) :end)
        ((< (len prefix) *fn-feed-journal-prefix-size*) :repair)
        ((not (equal (len prefix) *fn-feed-journal-prefix-size*)) :invalid)
        (t (let ((n (fn-cbor-u32-from prefix)))
             (if (and (<= *fn-feed-journal-frame-min* n)
                      (<= n *fn-feed-journal-frame-max*))
                 n
               :invalid)))))
(verify-guards fn-feed-journal-prefix)

(defun fn-feed-journal-open-frame (frame)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp frame))
      (fn-frame-error :octets)
    (fn-feed-decode frame
      (fn-frame-trailer (fn-frame-protected-prefix frame)))))

(defun fn-feed-journal-wrap (frame)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-cbor-octet-listp frame)
                (<= (len frame) *fn-feed-journal-frame-max*)
                (fn-frame-result-okp (fn-feed-journal-open-frame frame))))
      :bad
    (append (fn-cbor-u32-bytes (len frame)) frame)))
(verify-guards fn-feed-journal-wrap)

; Result: (status safe-offset entry). safe-offset advances only over a
; complete verified frame for this peer. It is the sole truncate authority.
; Replay retains the existing fn-feed-apply-record semantics, not drivenp:
; config changes and historical no-op records are not retroactively refused.
(defun fn-feed-journal-scan (peer prefix frame offset)
  (declare (xargs :guard t))
  (let ((plan (fn-feed-journal-prefix prefix)))
    (cond ((equal plan :end) (list :end (nfix offset) nil))
          ((equal plan :repair) (list :repair (nfix offset) nil))
          ((not (natp plan)) (list :invalid (nfix offset) nil))
          ((< (len frame) plan) (list :repair (nfix offset) nil))
          ((not (equal (len frame) plan))
           (list :invalid (nfix offset) nil))
          (t (let ((decoded (fn-feed-journal-open-frame frame)))
               (if (and (fn-frame-result-okp decoded)
                        (equal (fn-feed-record-peer
                                (fn-frame-result-payload decoded)) peer))
                   (list :next (+ (nfix offset)
                                  *fn-feed-journal-prefix-size* plan)
                         (fn-feed-journal-entry
                          (fn-frame-result-kind decoded)
                          (fn-frame-result-payload decoded)))
                 (list :invalid (nfix offset) nil)))))))

; Physical barriers/cuts named in the model and host: creation/open,
; scan completion, suffix truncation, content barrier, feed directory barrier,
; store directory barrier, append write and append barrier. Every non-durable
; append result fences; there is no rollback arm and no unfence in this image.
(defun fn-feed-journal-phase-step (phase event)
  (declare (xargs :guard t))
  (cond ((equal phase :uncertain) :uncertain)
        ((member-equal event '(:failed :crash)) :uncertain)
        ((and (equal phase :closed) (equal event :opened)) :scan)
        ((and (equal phase :scan) (equal event :repair)) :truncate)
        ((and (equal phase :truncate) (equal event :truncated)) :content)
        ((and (equal phase :scan) (equal event :end)) :content)
        ((and (equal phase :content) (equal event :content-durable)) :directory)
        ((and (equal phase :directory) (equal event :directory-durable)) :parent)
        ((and (equal phase :parent) (equal event :parent-durable)) :ready)
        ((and (equal phase :ready) (equal event :append)) :write)
        ((and (equal phase :write) (equal event :written)) :sync)
        ((and (equal phase :sync) (equal event :append-durable)) :ready)
        (t :uncertain)))

(defun fn-feed-journal-phase-run (phase events)
  (declare (xargs :guard t))
  (if (atom events) phase
    (fn-feed-journal-phase-run
     (fn-feed-journal-phase-step phase (car events)) (cdr events))))

; A suffix of physical observations cannot erase an uncertain result. This
; is an induction across arbitrary later events, not a single branch restated.
(defthm fn-feed-journal-uncertainty-survives-all-later-observations
  (equal (fn-feed-journal-phase-run :uncertain events) :uncertain))

; The actual scanner's accepted offset is strictly advancing and bounded;
; a host never consumes an unbounded peer-supplied length or repairs into
; accepted evidence. Non-next statuses preserve the last safe offset.
(defthm fn-feed-journal-next-is-bounded-progress
  (implies (equal (car (fn-feed-journal-scan peer prefix frame offset)) :next)
           (and (< (nfix offset)
                   (cadr (fn-feed-journal-scan peer prefix frame offset)))
                (<= (cadr (fn-feed-journal-scan peer prefix frame offset))
                    (+ (nfix offset) *fn-feed-journal-prefix-size*
                       *fn-feed-journal-frame-max*))))
  :hints (("Goal" :in-theory (disable fn-feed-journal-open-frame))))

(defthm fn-feed-journal-repair-preserves-accepted-offset
  (implies (equal (car (fn-feed-journal-scan peer prefix frame offset)) :repair)
           (equal (cadr (fn-feed-journal-scan peer prefix frame offset))
                  (nfix offset)))
  :hints (("Goal" :in-theory (disable fn-feed-journal-open-frame))))
