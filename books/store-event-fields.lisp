; fn: a Store event's four readings in one dispatch, for both event
; vocabularies (PKT-721; records-flip, 2026-09-27).
;
; books/store-events.lisp answers "is it an event, and what are its sequence,
; txid and generation" through four dispatchers per vocabulary, each of which
; re-runs the event recognizers from the first (a record recognizer walks the
; payload).  The history recognizer (books/replay-identity-index.lisp, over
; the RETAINED rows of fn-sf-records) and the pack-chain link check
; (books/checkpoint-pack-chain-once.lisp, over the decoded WIRE events of a
; link) each read all four at once.  They read them here, from ONE function:
; the two vocabularies differ only at an article (a held row, or a wire
; record) and at an accepted statement (the composite beside its interned
; article, or the wire composite), which WIREP selects; every other kind is
; the same event in both.
;
;   fn-event-fields-of-rows-is-the-dispatchers   WIREP nil: fn-store-event-p,
;                                                -sequence, -txid, -generation
;   fn-event-fields-of-wire-is-the-dispatchers   WIREP t: fn-wire-event-p,
;                                                -sequence, -txid, -generation
;
; Both with no hypothesis.

(in-package "ACL2")
(include-book "store-events")

(defun fn-event-fields (x wirep)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((if wirep (fn-record-p x) (fn-held-p x))
         (list t (fn-record-sequence x) (fn-record-txid x) (fn-record-generation x)))
        ((fn-store-retention-event-p x)
         (list t (fn-store-event-nth 2 x) (fn-store-event-nth 3 x)
               (fn-store-event-nth 4 x)))
        ((fn-stxe-p x) (list t (fn-stxe-sequence x) (fn-stxe-txid x)
                             (fn-stxe-generation x)))
        ((fn-stxk-p x) (list t (fn-stxk-sequence x) (fn-stxk-txid x)
                             (fn-stxk-generation x)))
        ((if wirep (fn-stxa-p x) (fn-hstxa-p x))
         (let ((a (if wirep x (fn-hstxa-stxa x))))
           (list t (fn-stxa-sequence a) (fn-stxa-txid a) (fn-stxa-generation a))))
        ((fn-cpe-eventp x) (list t (fn-cpe-sequence x) (fn-cpe-txid x)
                                 (fn-cpe-generation x)))
        ((fn-th-topic-eventp x) (list t (fn-th-at 1 x) (fn-th-at 2 x)
                                      (fn-th-at 3 x)))
        (t (list nil nil nil nil))))

(verify-guards fn-event-fields)

(defthm fn-event-fields-of-rows-is-the-dispatchers
  (equal (fn-event-fields x nil)
         (list (if (fn-store-event-p x) t nil) (fn-store-event-sequence x)
               (fn-store-event-txid x) (fn-store-event-generation x)))
  :hints (("Goal" :in-theory (e/d (fn-store-event-p fn-store-event-sequence
                                   fn-store-event-txid fn-store-event-generation)
                                  (fn-held-p fn-store-retention-event-p fn-stxe-p
                                   fn-stxk-p fn-hstxa-p fn-cpe-eventp
                                   fn-th-topic-eventp)))))

(defthm fn-event-fields-of-wire-is-the-dispatchers
  (equal (fn-event-fields x t)
         (list (if (fn-wire-event-p x) t nil) (fn-wire-event-sequence x)
               (fn-wire-event-txid x) (fn-wire-event-generation x)))
  :hints (("Goal" :in-theory (e/d (fn-wire-event-p fn-wire-event-sequence
                                   fn-wire-event-txid fn-wire-event-generation)
                                  (fn-record-p fn-store-retention-event-p fn-stxe-p
                                   fn-stxk-p fn-stxa-p fn-cpe-eventp
                                   fn-th-topic-eventp)))))

(in-theory (disable fn-event-fields))
