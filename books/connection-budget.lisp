; fn: what a served connection costs (lane connection-multiplexing, 2026-09-26;
; PKT-605; HST-024).
;
; The native host serves every reader and transit connection from a fixed set
; of I/O loop threads (host/native/mux.lisp), so a connection costs no thread;
; what it costs is bounded state, and this book names it:
;
;   HEAP PART, inside the dynamic space (octets):
;     record  the loop's connection record, its socket object and the
;             owner's connection record and session, measured
;             (*fn-cbud-record-octets*);
;     read    what the connection holds of its input: the retained suffix
;             (at most one read less one octet) and the read in hand, two
;             reads of the largest size a step may read
;             (fn-cbud-step-read-octets: 4 KiB), 2 x 4,096;
;     reply   the one reply a connection holds while the socket drains it
;             (the loop never steps a connection with a reply queued): an
;             article of the profile's A octets rendered, at most 2A + 1,024
;             (every line dot-stuffed and the status line);
;     compress the COMPRESS DEFLATE layer's inflater (RFC 8054; lane
;             compress): the 32 KiB window, the Huffman table, one read of
;             output and two of input, 56 KiB (*fn-cbud-compress-heap-octets*,
;             fn-cbud-compress-heap-covers-the-inflater); every connection is
;             charged it, since any authenticated one may start a layer;
;     parser  the wire state's command line, an octet list of at most one
;             line (512 octets), 16 octets of heap per octet
;             (*fn-heap-octets-per-list-octet*), twice for the collector's
;             copy.
;   NATIVE PART, outside it:
;     kernel  the socket's kernel buffers at their defaults, measured;
;     deflate zlib's outbound stream of a COMPRESS layer
;             (books/nntp-compress.lisp fn-zc-deflate-state-octets), 56 KiB;
;     tls     OpenSSL's or LibreSSL's session with SSL_MODE_RELEASE_BUFFERS
;             (host/native/tls.lisp), measured, when a TLS context is
;             loaded (implicit TLS or STARTTLS reachable);
; and the TLS handshakes' scratch (PRF-986: fn-cbud-handshake-octets).
;
; The memory equation charges these terms (books/memory-model.lisp: the
; connections' fn-cbud-conn-octets, the handshakes' fn-cbud-handshake-octets),
; and the run's capacity is its gate's C' (books/admission-memory.lisp
; fn-adm-capacity, at configure and after each live reconfiguration:
; host/owner-host.lisp fn-owner-memory-configure, fn-owner-memory-recapacity,
; and fn-owner-memory-candidate-refusal, which refuses by name a raise the
; gate does not hold).  PRF-223's statement, the capacity a process holds, is
; that gate's (fn-adm-capacity-fits, fn-adm-capacity-is-the-most) since
; L-RUN-LAUNCH, which retired this book's own resident model of the run (the
; profile's whole store and every thread's runtime charged as resident, the
; dynamic space compared with the machine: a twin of the equation that
; refused the fresh start at 256 MiB on fn-core and at 1024 MiB on fn-host).
;
; The read size of a served step: `fn-cbud-step-read-octets' (bounded by
; *fn-cbud-read-quantum*, `fn-cbud-step-read-octets-is-bounded'; 512 under
; a step rate, `fn-cbud-step-read-octets-under-a-rate-by-definition'; held by the figure,
; `fn-cbud-read-covers-the-step'), called through host/owner-host.lisp
; fn-owner-read-octets by host/native/owner.lisp fnn-owner-refresh-read-octets.

(in-package "ACL2")
(include-book "heap-figure")
(include-book "public-exposure")
(include-book "profile-limits") ; its figures are rows there
(include-book "nntp-compress")
(include-book "deflate-inflate")

; -----------------------------------------------------------------------------
; The per-connection figure.  The measured constants are pinned by the native
; witness (tests/test_native_mux.py) and recorded with their runs in
; planning/evidence/connection-multiplexing-2026-09-26.md.

; -----------------------------------------------------------------------------
; The host read: the work one served step may do (D27; lane input-loop-2).
; A served step is one fn-owner-chunk-span-at over at most one host read, and the
; read's size is decided here, from the exposure limits in force.  Under a
; step rate (exposure-steps-per-second; the public default is 64), a step is
; the rate's unit of work and reads at most *fn-cbud-step-octets* (512, RFC
; 3977 section 3.1's command line), so the rate keeps its meaning in octets
; per second.  Without one (a loopback listener, or a row set to 0), a step
; reads at most *fn-cbud-read-quantum* (4 KiB): a 10 MiB POST is 2,560 owner
; steps, not 20,480.  The quantum is the measured trade (planning/evidence/
; input-loop-2-2026-09-27.md section 5): a step holds the owner mutex for
; about 100 ns per octet it reads, so another connection's command waits
; for up to one step -- during a 1 MiB upload a DATE client's median was
; 0.44 ms at 512, 0.62 ms at 4 KiB, 1.10 ms at 16 KiB and 3.84 ms at 64 KiB
; -- while the allocation per POSTed octet is 592.5, 571.1, 568.8 and 568.0
; octets: 4 KiB takes 97% of the per-step saving for a fifth of a
; millisecond.  Raise it when the per-octet cost of a step falls (the body
; out of the parser's lists: item 2 of that record).  The host reads the answer under the owner mutex after every step
; (host/owner-host.lisp fn-owner-read-octets; host/native/owner.lisp
; fnn-owner-refresh-read-octets) and reads into one buffer per I/O loop, so
; a read allocates only the octets it returns.
(include-book "connection-read-quantum")

(defconst *fn-cbud-record-octets* 16384)
; The retained suffix (less than one read) and the read in hand: two reads
; of the largest size any limits give (fn-cbud-read-covers-the-step).
(defconst *fn-cbud-read-octets* (* 2 *fn-cbud-read-quantum*))
(defconst *fn-cbud-line-octets* 512)
(defconst *fn-cbud-reply-status-octets* 1024)
(defconst *fn-cbud-kernel-octets* 212992)
(defconst *fn-cbud-tls-octets* 131072)
(defconst *fn-cbud-compress-heap-octets* 57344)
(defconst *fn-cbud-compress-native-octets* 57344)

; The two COMPRESS terms hold what a layer allocates: the inflater's window
; and table (fn-zin-buffer-sizes), its output (one read) and its input (two
; reads); zlib's state for the parameters ACL2 gives it.
(defthm fn-cbud-compress-heap-covers-the-inflater
  (<= (+ *fn-zin-window* *fn-zin-tab-octets* (* 3 *fn-cbud-read-quantum*))
      *fn-cbud-compress-heap-octets*)
  :rule-classes nil)

(defthm fn-cbud-compress-native-covers-zlib
  (<= (fn-zc-deflate-state-octets) *fn-cbud-compress-native-octets*)
  :rule-classes nil)

; The heap term also holds the outbound side's buffer: one window's
; compressed output under the flush schedule (books/nntp-compress.lisp
; fn-zc-sync-output-octets of fn-zc-window-octets), next to the inflater.
(defthm fn-cbud-compress-heap-covers-the-layer
  (<= (+ *fn-zin-window* *fn-zin-tab-octets* (* 3 *fn-cbud-read-quantum*)
         (fn-zc-sync-output-octets (fn-zc-window-octets)))
      *fn-cbud-compress-heap-octets*)
  :rule-classes nil)

;; THE HANDSHAKES (PRF-986, books/tls-handshake-budget.lisp; lane
;; tls-handshake-budget-2).  A TLS handshake in progress holds native memory
;; beyond its connection's established session (*fn-cbud-tls-octets*):
;; OpenSSL's or LibreSSL's two record buffers (16,709 octets each at their
;; defaults) and the handshake's transcript, key exchange and certificate
;; chain, *fn-cbud-handshake-scratch-octets* (stated, not measured: measure
;; at convergence, the TLS native module's flood against L).  It is the
;; library's malloc, outside the dynamic space, so the memory equation charges
;; it beside the heap (books/memory-model.lisp fn-mm-inflight), not the credit
;; ledger (books/memory-credits: dynamic-space credits).  The handshake budget
;; admits at most L at once (`tls-handshakes-in-flight',
;; fn-hsb-steps-keep-the-bound), so the term is L x the scratch whenever a TLS
;; context is loaded.
(defconst *fn-cbud-handshake-scratch-octets* 131072)

;; L: the live row, the profile's default when the row is absent (the same
;; resolution as books/tls-handshake-budget.lisp fn-hsb-lim-in-flight,
;; `fn-hsb-lim-in-flight-is-the-charged-slots').
(defun fn-cbud-handshake-slots (tlsp inflight)
  (declare (xargs :guard t))
  (if tlsp
      (if (posp inflight) inflight (fn-profile-limit :tls-handshakes-in-flight))
    0))

(defun fn-cbud-handshake-octets (tlsp inflight)
  (declare (xargs :guard t))
  (* (nfix (fn-cbud-handshake-slots tlsp inflight)) *fn-cbud-handshake-scratch-octets*))

;; The configuration's row (the host's call: fn-owner-connection-budget).
(defun fn-cbud-config-handshake-slots (v tlsp)
  (declare (xargs :guard t))
  (fn-cbud-handshake-slots tlsp (fn-cfg-limit v "tls-handshakes-in-flight")))

(defthm fn-cbud-handshake-octets-natp
  (natp (fn-cbud-handshake-octets tlsp inflight))
  :rule-classes :type-prescription)

(defun fn-cbud-conn-heap-octets (article)
  (declare (xargs :guard t))
  (+ *fn-cbud-record-octets*
     *fn-cbud-read-octets*
     (+ (* 2 (nfix article)) *fn-cbud-reply-status-octets*)
     (* 2 *fn-heap-octets-per-list-octet* *fn-cbud-line-octets*)
     *fn-cbud-compress-heap-octets*))

(defun fn-cbud-conn-native-octets (tlsp)
  (declare (xargs :guard t))
  (+ *fn-cbud-kernel-octets* *fn-cbud-compress-native-octets*
     (if tlsp *fn-cbud-tls-octets* 0)))

; The per-connection figure holds a step's read and its suffix under any
; limits.
(defthm fn-cbud-read-covers-the-step
  (<= (* 2 (fn-cbud-step-read-octets lim)) *fn-cbud-read-octets*)
  :rule-classes :linear)

(defthm fn-cbud-conn-heap-octets-posp
  (posp (fn-cbud-conn-heap-octets article))
  :rule-classes :type-prescription)

(defthm fn-cbud-conn-native-octets-posp
  (posp (fn-cbud-conn-native-octets tlsp))
  :rule-classes :type-prescription)

(defun fn-cbud-conn-octets (article tlsp)
  (declare (xargs :guard t))
  (+ (fn-cbud-conn-heap-octets article) (fn-cbud-conn-native-octets tlsp)))

(defthm fn-cbud-conn-octets-posp
  (posp (fn-cbud-conn-octets article tlsp))
  :rule-classes :type-prescription)

; A refused TLS connection's line (host/native/mux.lisp).
(defconst *fn-cbud-tls-reasons*
  '((:handshake . "handshake") (:timeout . "timeout") (:closed . "closed")
    (:refused . "refused") (:busy . "busy")))

(defun fn-cbud-tls-refusal-line (reason id)
  (declare (xargs :guard t))
  (let ((word (cdr (assoc-equal reason *fn-cbud-tls-reasons*))))
    (concatenate 'string "tls refused reason=" (if (stringp word) word "other")
                 " connection=" (fn-heap-decimal id))))

(defun fn-cbud-slots-octets (slots)
  (declare (xargs :guard t))
  (* (nfix slots) *fn-cbud-handshake-scratch-octets*))

(defthm fn-cbud-handshake-octets-is-the-slots
  (equal (fn-cbud-handshake-octets tlsp inflight)
         (fn-cbud-slots-octets (fn-cbud-handshake-slots tlsp inflight))))

