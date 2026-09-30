; Physical writer/journal and retained Store-authority decisions. This leaf
; proves scalar decisions only; the host must supply actual join observations.
(in-package "ACL2")

; A physical timeout retains the writer and its descriptor authority. Even
; an absent/joined writer is not settlement while accounted work remains.
(defun fn-ort-log-close-action (join-observation pending-lines pending-octets queuedp)
  (declare (xargs :guard t))
  (if (and (or (equal join-observation :joined)
               (equal join-observation :absent))
           (equal pending-lines 0) (equal pending-octets 0)
           (equal queuedp nil))
      :joined
    :held))

(defthm fn-ort-log-close-joined-requires-settlement
  (implies (equal (fn-ort-log-close-action observation lines octets queuedp) :joined)
           (and (or (equal observation :joined) (equal observation :absent))
                (equal lines 0) (equal octets 0) (equal queuedp nil)))
  :rule-classes nil)

(defun fn-ort-log-close-exit (prior uncertain action)
  (declare (xargs :guard (and (integerp prior) (integerp uncertain))))
  (if (equal action :joined) prior uncertain))

(defthm fn-ort-log-close-held-is-uncertain
  (implies (not (equal action :joined))
           (equal (fn-ort-log-close-exit prior uncertain action) uncertain)))

(defun fn-ort-report-close-action (log-action journal-observation)
  (declare (xargs :guard t))
  (if (and (equal log-action :joined)
           (or (equal journal-observation :closed)
               (equal journal-observation :absent)))
      :joined
    :held))

(defthm fn-ort-report-close-requires-journal-settlement
  (implies (equal (fn-ort-report-close-action log-action observation) :joined)
           (and (equal log-action :joined)
                (or (equal observation :closed) (equal observation :absent))))
  :rule-classes nil)

; The native writer slot remains present after timeout and is cleared only
; after definite join. This decides authority over its log descriptor only,
; not settlement of the complete owner producer graph.
(defun fn-ort-log-caller-action (writer-presentp)
  (declare (xargs :guard t))
  (if (equal writer-presentp nil) :write-close :held))

(defthm fn-ort-log-caller-held-preserves-descriptor-authority
  (implies (not (equal writer-presentp nil))
           (equal (fn-ort-log-caller-action writer-presentp) :held)))


; An unsettled writer/journal may still mutate the decision journal under the
; Store lock. Even when no live writer slot remains, accounted debt can hold it.
(defun fn-ort-store-close-action (settlement authority-presentp caller-fd-presentp)
  (declare (xargs :guard t))
  (cond ((not (equal settlement :joined)) :held)
        ((equal authority-presentp nil) :settled)
        ((not (equal caller-fd-presentp nil)) :defer)
        (t :close)))

(defun fn-ort-service-settlement-action (settlement store-observation)
  (declare (xargs :guard t))
  (if (and (equal settlement :joined)
           (or (equal store-observation :closed)
               (equal store-observation :absent)))
      :joined :held))

(defun fn-ort-service-start-action (writer-presentp authority-presentp)
  (declare (xargs :guard t))
  (if (and (equal writer-presentp nil) (equal authority-presentp nil))
      :start :held))

(defun fn-ort-service-claim-action (writer-presentp authority-presentp reservation-ownedp)
  (declare (xargs :guard t))
  (if (and (equal writer-presentp nil)
           (or (equal authority-presentp nil) (equal reservation-ownedp t)))
      :start :held))

(defthm fn-ort-service-claim-requires-no-writer-and-own-authority
  (implies (equal (fn-ort-service-claim-action writer authority owned) :start)
           (and (equal writer nil)
                (or (equal authority nil) (equal owned t))))
  :rule-classes nil)

(defun fn-ort-service-start-reason (action)
  (declare (xargs :guard t))
  (if (equal action :held) "prior owner authority is unsettled" ""))

(defthm fn-ort-store-close-requires-settled-producers
  (implies (equal (fn-ort-store-close-action settlement authority caller) :close)
           (and (equal settlement :joined) (not (equal authority nil))
                (equal caller nil)))
  :rule-classes nil)

(defthm fn-ort-service-release-requires-store-settlement
  (implies (equal (fn-ort-service-settlement-action settlement observation) :joined)
           (and (equal settlement :joined)
                (or (equal observation :closed) (equal observation :absent))))
  :rule-classes nil)

(defthm fn-ort-service-start-requires-no-prior-authority
  (implies (equal (fn-ort-service-start-action writer authority) :start)
           (and (equal writer nil) (equal authority nil)))
  :rule-classes nil)

(in-theory (disable fn-ort-log-close-action fn-ort-log-close-exit
                    fn-ort-report-close-action fn-ort-log-caller-action
                    fn-ort-store-close-action fn-ort-service-settlement-action
                    fn-ort-service-start-action fn-ort-service-claim-action fn-ort-service-start-reason))
