; fn: proactive fragmentation of an outbound bundle (spike/bp).
;
; RFC 9171 section 5.8: a bundle whose "bundle must not be fragmented" flag
; is clear MAY be fragmented; every fragment carries the parent's identity
; (source, creation time, sequence), the fragment flag, its offset into the
; ADU and the ADU's total length; its payload is one contiguous extent of
; the parent's payload.  "Each extension block whose 'Block must be
; replicated in every fragment' flag is set to 1 SHALL be replicated in
; every fragment"; beyond that the choice is the BPA's.  fn replicates EVERY
; extension block in every fragment (a fragment is a bundle, and a bundle
; whose creation time is zero needs its Bundle Age block, section 4.4.2).
;
; RFC 9174 section 5.4.? (Transfer MRU): a TCPCLv4 entity SHALL NOT send a
; transfer longer than the peer's Transfer MRU.  Segmenting within one
; transfer (Segment MRU) is TCPCL's own concern and fn's session machine
; does it; a BUNDLE longer than the peer's Transfer MRU must be fragmented
; at the BP layer or not sent.  fn-bpfs-plan answers which.
;
;; SPIKE: :program mode; defers (a) the theorem that the fragments' payload
;; extents reassemble exactly to the parent payload and each fragment
;; unfragments to the parent primary (fn-bpfs-reassembles-exactly, stated
;; in planning/evidence/spike-bp-2026-09-25.md; the test book witnesses it),
;; (b) per-fragment custody records: the base job's one attempt covers all
;; of its fragments and the host reads the transfer as accepted only when
;; every fragment's transfer was acknowledged.
(in-package "ACL2")
(include-book "bp-fragment")
(include-book "bp-bundle")
(program)

; The fragment of BUNDLE whose payload is BYTES at ADU offset OFFSET.  A
; parent that is itself a fragment keeps its ADU coordinates.
(defun fn-bpfs-fragment (bundle offset bytes)
  (let* ((p (fn-bpb-bundle-primary bundle))
         (parentp (fn-bpp-fragmentp (fn-bpp-flags p)))
         (primary (if parentp
                      (fn-bpf-refragment-block p offset)
                    (fn-bpf-fragment-block p offset
                                           (len (fn-bpb-payload bundle)))))
         (payload (fn-bpb-bundle-payload bundle)))
    (fn-bpb-make-bundle
     primary (fn-bpb-bundle-blocks bundle)
     (fn-bpb-make-block (fn-bpb-block-type payload) (fn-bpb-block-number payload)
                        (fn-bpb-block-flags payload) (fn-bpb-block-crc-type payload)
                        bytes))))

; The encoded length of a fragment carrying no payload octets, at the
; largest offset it can name: every fragment's overhead is at most this.
(defun fn-bpfs-overhead (bundle)
  (let ((total (len (fn-bpb-payload bundle))))
    (len (fn-bpb-encode (fn-bpfs-fragment bundle total nil)))))

(defun fn-bpfs-cut (bundle payload offset chunk acc)
  (if (atom payload)
      (reverse acc)
    (let ((n (min chunk (len payload))))
      (fn-bpfs-cut bundle (nthcdr n payload) (+ offset n) chunk
                   (cons (fn-bpb-encode
                          (fn-bpfs-fragment bundle offset (take n payload)))
                         acc)))))

; (:whole)                 WIRE fits MRU: send it as it is;
; (:fragments W1 ... Wn)   the fragments' wires, each at most MRU octets,
;                          in offset order;
; (:refused REASON)        :malformed, :no-fragment (the flag forbids it),
;                          :mru-too-small (no payload octet fits).
(defun fn-bpfs-plan (wire mru)
  (cond
   ((not (and (natp mru) (fn-cbor-octet-listp wire))) (list :refused :malformed))
   ((<= (len wire) mru) (list :whole))
   (t
    (let ((r (fn-bpb-decode wire (len wire))))
      (if (not (fn-cbor-result-okp r))
          (list :refused :malformed)
        (let* ((bundle (fn-cbor-result-value r))
               (p (fn-bpb-bundle-primary bundle)))
          (if (fn-bpp-no-fragmentp (fn-bpp-flags p))
              (list :refused :no-fragment)
            ;; A byte string's CBOR head grows by at most 8 octets with its
            ;; length, over the empty payload the overhead measured.
            (let ((chunk (- mru (+ 8 (fn-bpfs-overhead bundle)))))
              (if (<= chunk 0)
                  (list :refused :mru-too-small)
                (cons :fragments
                      (fn-bpfs-cut bundle (fn-bpb-payload bundle) 0 chunk
                                   nil)))))))))))

; The fragments' (offset bytes total) views, decoded back from their wires:
; what a receiver's family reassembly consumes.
(defun fn-bpfs-views (wires)
  (if (atom wires)
      nil
    (let* ((b (fn-cbor-result-value (fn-bpb-decode (car wires) (len (car wires)))))
           (p (fn-bpb-bundle-primary b)))
      (cons (fn-bpf-make (fn-bpp-fragment-offset p) (fn-bpb-payload b)
                         (fn-bpp-total-adu-length p))
            (fn-bpfs-views (cdr wires))))))

(defun fn-bpfs-max-len (wires)
  (if (atom wires) 0 (max (len (car wires)) (fn-bpfs-max-len (cdr wires)))))
