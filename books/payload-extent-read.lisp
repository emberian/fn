; fn: the served read's entry check over an octet buffer (lane
; arena-offheap-3, 2026-09-27; PRF-295, P3's first consumer).
;
; The realizer of an extent handle (host/native/extent.lisp) preads the log
; entry's protected prefix and its 32-octet trailer.  It used to hand ACL2
; the whole entry as an octet list (fn-arx-entry-ok, books/payload-extent.lisp:
; elen + 32 conses per read, SHA-256 by car/cdr); now it fills its own octet
; buffer `fn-octets-rd' with the prefix, in place, and ACL2 decides
; `fn-arx-entry-ok-buffer': the frame digest of the buffer
; (`fn-frame-digest-buffer', books/frame-digest-buffer.lisp, read by index)
; is the trailer.  KEYSTONE fn-arx-entry-ok-buffer-is-the-frame-check: that is
; the log's own frame check on the prefix's octets (the entry's trailer is
; fn-frame-digest of its protected prefix: books/store-log.lisp fn-lg-frame
; through fn-frame-seal), and fn-arx-entry-ok-buffer-of-durable: a faithful
; read of an intact entry passes.

(in-package "ACL2")
(include-book "frame-digest-buffer")
(include-book "payload-extent")

; The realizer's buffer: its own live object, congruent to fn-octets (the
; served attempt's buffer is never touched by a read of an extent handle).
(defabsstobj fn-octets-rd
  :foundation fn-octets$c
  :recognizer (fn-octets-rd-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-octets-rd :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-octets-rd-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-octets-rd-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-octets-rd-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-octets-rd-append-octet :logic fn-octets$a-append-octet
                                       :exec fn-octets$c-append-octet :protect t)
            (fn-octets-rd-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-octets-rd-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                  :protect t)
            (fn-octets-rd-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-octets-rd-from-list :logic fn-octets$a-from-list
                                    :exec fn-octets$c-from-list :protect t)
            (fn-octets-rd-append-list :logic fn-octets$a-append-list
                                      :exec fn-oct-write-list :protect t)
            (fn-octets-rd-append-back :logic fn-octets$a-append-back
                                      :exec fn-octets$c-append-back :protect t)
            (fn-octets-rd-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-octets-rd-append-word :logic fn-octets$a-append-word
                                      :exec fn-octets$c-append-word :protect t))
  :congruent-to fn-octets)

; The check the realizer asks: the buffer holds the entry's protected prefix,
; TRAILER the 32 octets read after it.
(defun fn-arx-entry-ok-buffer (trailer fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (equal (fn-frame-digest-buffer nil fn-octets) trailer))

; KEYSTONE (PRF-295).  The buffer check is the frame check on the prefix's
; octets: the host's check (host/native/extent.lisp fnn-extent-entry calls
; fn-arx-entry-ok-buffer over fn-octets-rd) decides what the list check on
; the same octets decides.
(defthm fn-arx-entry-ok-buffer-is-the-frame-check
  (equal (fn-arx-entry-ok-buffer trailer fn-octets)
         (equal (fn-frame-digest fn-octets) trailer)))

; A faithful read of an intact entry passes: the buffer holds the durable
; prefix, TRAILER the durable trailer, and the file's trailer is the frame
; digest of its prefix (what the log's append wrote, A-DURABLE-EXTENT).
(defthm fn-arx-entry-ok-buffer-of-durable
  (implies (equal (fn-durable-octets file (+ eoff elen) *fn-frame-trailer-octets*)
                  (fn-frame-digest (fn-durable-octets file eoff elen)))
           (fn-arx-entry-ok-buffer (fn-durable-octets file (+ eoff elen) *fn-frame-trailer-octets*)
                                   (fn-durable-octets file eoff elen)))
  :hints (("Goal" :in-theory (disable fn-durable-octets-len))))

; -----------------------------------------------------------------------------
; The read decided against the descriptor's COMMITMENT (lane extent-identity,
; 2026-09-29; PRF-994; GPT-6's warranty-quality-proof-engineering.md
; section 2).
;
; The buffer holds the protected prefix the host read at [EOFF, EOFF+ELEN),
; READ the 32 octets it read after that, EXPECTED the descriptor's trailer
; (books/payload-extent.lisp fn-arx-trailer-nat of the entry's recorded
; trailer, attached to the record's place when the descriptor was made).
; The verdict, each refused by name by the realizer (host/native/extent.lisp
; fnn-extent-entry):
;   :trailer  the trailer recorded after the prefix is not the descriptor's
;             (another entry at this offset, a wrong offset, an entry of
;             another store or generation: the recorded trailer disagrees
;             with the commitment, however well formed the entry is);
;   :digest   the recorded trailer is the descriptor's but the prefix's
;             frame digest is not it (the prefix was damaged in place);
;   :ok       the prefix's digest is the recorded trailer and that trailer is
;             the descriptor's.
; Nothing else is answered: a malformed READ is :trailer.
(defun fn-arx-entry-verdict-buffer (expected read fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (cond ((not (and (fn-cbor-octet-listp read)
                   (equal (len read) *fn-frame-trailer-octets*)
                   (equal (fn-arx-trailer-nat read) expected)))
         :trailer)
        ((not (equal (fn-frame-digest-buffer nil fn-octets) read)) :digest)
        (t :ok)))

; KEYSTONE (PRF-994).  The verdict is :ok exactly when the read's recorded
; trailer is the descriptor's commitment and the prefix's frame digest is
; that trailer: what fn-arx-entry-ok-buffer decided, AND the identity it
; never decided.
(defthm fn-arx-entry-verdict-buffer-ok-is-the-commitment
  (equal (equal (fn-arx-entry-verdict-buffer expected read fn-octets) :ok)
         (and (fn-cbor-octet-listp read)
              (equal (len read) *fn-frame-trailer-octets*)
              (equal (fn-arx-trailer-nat read) expected)
              (equal (fn-frame-digest fn-octets) read))))

; The refusals are distinct and exhaustive: a verdict is one of the three.
(defthm fn-arx-entry-verdict-buffer-is-one-of-three
  (member-equal (fn-arx-entry-verdict-buffer expected read fn-octets) '(:ok :trailer :digest))
  :rule-classes nil)

; KEYSTONE (PRF-994), the boundary composed with the descriptor: when
; EXPECTED is the commitment of the entry's durable recorded trailer (the 32
; octets the file holds after the prefix at [EOFF, EOFF+ELEN)), an :ok
; verdict means the frame digest of the buffer the host serves from IS that
; recorded trailer -- the octets the host hands to the model are the octets
; whose digest the accepted extent committed to (fn-arx-trailer-nat-injective:
; no other 32 octets have that commitment).  A-DURABLE-EXTENT names the
; durable octets; the collision figure of the digest (pessimistic: a BLAKE3
; collision, 2^128 work) is the only gap between "the same digest" and "the
; same octets".
(defthm fn-arx-entry-verdict-buffer-ok-digest-is-the-recorded-trailer
  (implies (equal (fn-arx-entry-verdict-buffer
                   (fn-arx-trailer-nat (fn-durable-octets file (+ eoff elen) *fn-frame-trailer-octets*))
                   read fn-octets)
                  :ok)
           (equal (fn-frame-digest fn-octets)
                  (fn-durable-octets file (+ eoff elen) *fn-frame-trailer-octets*)))
  :hints (("Goal"
           :use ((:instance fn-arx-trailer-nat-injective
                            (a read)
                            (b (fn-durable-octets file (+ eoff elen) *fn-frame-trailer-octets*))))
           :in-theory (disable fn-durable-octets-len))))

; No false refusal: a faithful read of an intact entry (the buffer holds the
; durable prefix, READ the durable trailer, the file's trailer the frame
; digest of its prefix) against the descriptor made from that trailer is :ok.
(defthm fn-arx-entry-verdict-buffer-of-durable
  (implies (equal (fn-durable-octets file (+ eoff elen) *fn-frame-trailer-octets*)
                  (fn-frame-digest (fn-durable-octets file eoff elen)))
           (equal (fn-arx-entry-verdict-buffer
                   (fn-arx-trailer-nat (fn-durable-octets file (+ eoff elen) *fn-frame-trailer-octets*))
                   (fn-durable-octets file (+ eoff elen) *fn-frame-trailer-octets*)
                   (fn-durable-octets file eoff elen))
                  :ok))
  :hints (("Goal" :in-theory (disable fn-durable-octets-len))))

(in-theory (disable fn-arx-entry-verdict-buffer))

; -----------------------------------------------------------------------------
; The commitment read from a buffer, by index (the open's entry buffer, the
; publication's frame buffer): the twins of fn-arx-trailer-nat-at and
; fn-arx-attach-trailers over fn-octets, equal to them over the buffer's
; octets (KEYSTONE fn-arx-attach-trailers-buffer-is-attach-trailers).

(defun fn-arx-trailer-nat-at-buffer (j fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp j) (<= (+ j *fn-frame-trailer-octets*) (fn-octets-len fn-octets)))))
  (fn-arx-trailer-nat (fn-oct-slice-list j (+ j *fn-frame-trailer-octets*) fn-octets)))

(defthm fn-arx-trailer-nat-at-buffer-is-trailer-nat-at
  (implies (and (fn-octets-p fn-octets) (natp j)
                (<= (+ j *fn-frame-trailer-octets*) (len fn-octets)))
           (equal (fn-arx-trailer-nat-at-buffer j fn-octets)
                  (fn-arx-trailer-nat-at j fn-octets)))
  :hints (("Goal" :in-theory (enable fn-octets-p))))

; The places of the entry the buffer holds (books/store-log-buffer.lisp
; fn-lgb-entry-places: START is BASE, the entry's file offset, for each), with
; the entry's commitment attached.
(defun fn-arx-attach-trailers-buffer (places base fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (true-listp places) (natp base))))
  (if (atom places)
      nil
    (cons (if (true-listp (car places))
              (let* ((start (nfix (nth 0 (car places))))
                     (n (nfix (nth 1 (car places))))
                     (j (nfix (- (+ start n) (+ base *fn-frame-trailer-octets*)))))
                (list (nth 0 (car places)) (nth 1 (car places)) (nth 2 (car places))
                      (nth 3 (car places))
                      (if (<= (+ j *fn-frame-trailer-octets*) (fn-octets-len fn-octets))
                          (fn-arx-trailer-nat-at-buffer j fn-octets)
                        (fn-arx-trailer-nat-at j (fn-octets-list fn-octets)))))
            (car places))
          (fn-arx-attach-trailers-buffer (cdr places) base fn-octets))))

(defthm fn-arx-attach-trailers-buffer-is-attach-trailers
  (implies (fn-octets-p fn-octets)
           (equal (fn-arx-attach-trailers-buffer places base fn-octets)
                  (fn-arx-attach-trailers places base fn-octets)))
  :hints (("Goal" :in-theory (enable fn-octets-p))))
