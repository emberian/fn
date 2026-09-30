; fn: what a served connection costs, and how many a process holds
; (lane connection-multiplexing, 2026-09-26; PKT-605; HST-024; PRF-223).
;
; Until this book nothing checked the connection capacity (the
; `exposure-connections' row, PRF-211) against memory: each connection was a
; worker thread with its own control stack, and books/heap-figure.lisp sizes
; only the dynamic space for the store.  The native host now serves every
; reader and transit connection from a fixed set of I/O loop threads
; (host/native/mux.lisp), so a connection costs no thread; what it costs is
; bounded state, and this book names it, derives the most connections the
; process holds from what the host observes, and decides the capacity
; against it:
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
;             (the loop never steps a connection with a reply queued): the
;             STATED WORKLOAD's largest, an article of the profile's A
;             octets rendered, at most 2A + 1,024 (every line dot-stuffed
;             and the status line).  A reply larger than that (an OVER or
;             LISTGROUP over a large range) is outside the stated workload
;             until the owner renders replies in windows (PKT-644);
;     compress the COMPRESS DEFLATE layer's inflater (RFC 8054; lane
;             compress): the 32 KiB window, the Huffman table, one read of
;             output and two of input (a read and the compressed octets a
;             stopped call left), 56 KiB (*fn-cbud-compress-heap-octets*,
;             fn-cbud-compress-heap-covers-the-inflater); every connection is
;             charged it, since any authenticated one may start a layer;
;     parser  the wire state's command line, an octet list of at most one
;             line (512 octets), 16 octets of heap per octet
;             (*fn-heap-octets-per-list-octet*), twice for the collector's
;             copy.  The BODY of an article in flight is not a per-connection
;             term since lane zero-copy-commit: the dynamic space holds
;             `fn-heap-article-slots' of them (books/heap-store-figure.lisp)
;             and the owner admits a connection into article mode only
;             within them (books/owner-article-slots.lisp); before, this term
;             was 32 x (512 + A) and charged to the machine only, so the heap
;             held none of it.
;   NATIVE PART, outside it:
;     kernel  the socket's kernel buffers at their defaults, measured;
;     deflate zlib's outbound stream of a COMPRESS layer
;             (books/nntp-compress.lisp fn-zc-deflate-state-octets), 56 KiB;
;     tls     OpenSSL's or LibreSSL's session with SSL_MODE_RELEASE_BUFFERS
;             (host/native/tls.lisp), measured, when a TLS context is
;             loaded (implicit TLS or STARTTLS reachable).
;
; The base the connections come on top of is the process without them (the
; brief's "heap figure"): heap-figure's figure for the store (HNEED:
; books/heap-figure.lisp fn-heap-figure-octets, the dynamic space the store's
; profile needs), the core's mappings outside the dynamic space (CORE, the
; file's length, as heap-figure counts it), and THREADS fixed threads (the
; loops, accept threads, control clients, the log writer, the publication,
; feeds) each with its control stack (STACK, observed) and the runtime's
; per-thread regions (*fn-cbud-thread-runtime-octets*, image-floor's 4 MiB).
; The claim is resident memory under the stated workload.  The dynamic space
; holds the store's figure, which since lane zero-copy-commit includes the
; articles in flight (the bodies and queued submissions, admitted within
; `fn-heap-article-slots'); the rest of each connection's heap part (record,
; reads, reply, command line) is charged to the machine here and NOT held by
; the dynamic space: a reply of the stated workload is 2A + 1,024 octets a
; connection, so many readers of the largest article at once can still
; exhaust the heap until replies are rendered in windows (PKT-644).
;
; KEYSTONE `fn-cbud-bound-holds-its-connections': the base and N
; connections, N at most the bound, fit the machine.
; `fn-cbud-bound-is-the-most': one more does not.
; KEYSTONE `fn-cbud-run-decide-holds-the-capacity': an accepted run holds
; its capacity; `fn-cbud-run-decide-refuses-exactly-past-the-bound'.
; KEYSTONE `fn-cbud-admitted-connections-fit-the-machine': under an
; accepted capacity every connection fn-exp-open admits, trusted sources
; included (the trusted range exempts a source from the per-address rule
; only; the capacity counts every connection, PRF-211), leaves the process
; within the machine.
; `fn-cbud-deltas-refusal-keeps-the-capacity-held': a live reconfiguration
; the owner stages leaves the capacity within the bound the run installed.
;
; The read size of a served step: `fn-cbud-step-read-octets' (bounded by
; *fn-cbud-read-quantum*, `fn-cbud-step-read-octets-is-bounded'; 512 under
; a step rate, `fn-cbud-step-read-octets-under-a-rate-by-definition'; held by the figure,
; `fn-cbud-read-covers-the-step'), called through host/owner-host.lisp
; fn-owner-read-octets by host/native/owner.lisp fnn-owner-refresh-read-octets.
;
; Host callers: host/owner-host.lisp fn-owner-connection-budget (called by
; host/native/owner.lisp fnn-owner-run after recovery, before listen) and
; fn-owner-reconfigure-deltas (every live reconfiguration: native-admin,
; peer-invite, auth).

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
(defconst *fn-cbud-thread-runtime-octets* (* (fn-profile-limit :thread-runtime-mib) 1024 1024))
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
;; library's malloc, outside the dynamic space, so it is charged HERE, to the
;; machine, and not to the credit ledger (books/memory-credits: dynamic-space
;; credits).  The handshake budget admits at most L at once
;; (`tls-handshakes-in-flight', fn-hsb-steps-keep-the-bound), so the term is
;; L x the scratch whenever a TLS context is loaded, a fixed part of the
;; base like the threads.
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

; The process without connections: the store's heap figure, the core's
; mappings outside the dynamic space, and the fixed threads.
(defun fn-cbud-base-octets (hneed core threads stack hs)
  (declare (xargs :guard t))
  (+ (nfix hneed) (nfix core)
     (* (nfix threads) (+ (nfix stack) *fn-cbud-thread-runtime-octets*))
     (nfix hs)))

; The rest of the base: the core outside the dynamic space, the threads and
; the handshakes' scratch HS (fn-cbud-handshake-octets).
(defun fn-cbud-rest-octets (core threads stack hs)
  (declare (xargs :guard t))
  (+ (nfix core)
     (* (nfix threads) (+ (nfix stack) *fn-cbud-thread-runtime-octets*))
     (nfix hs)))

(defun fn-cbud-conn-octets (article tlsp)
  (declare (xargs :guard t))
  (+ (fn-cbud-conn-heap-octets article) (fn-cbud-conn-native-octets tlsp)))

(defthm fn-cbud-conn-octets-posp
  (posp (fn-cbud-conn-octets article tlsp))
  :rule-classes :type-prescription)

; The bound a run's decision holds (fn-cbud-run-decide below).
(defun fn-cbud-held-bound (decision)
  (declare (xargs :guard t))
  (if (and (consp decision) (equal (car decision) :hold) (consp (cdr decision)))
      (nfix (cadr decision))
    0))

; -----------------------------------------------------------------------------
; The lines.  The run's refusal (stderr and the service log, exit 1), and
; the connection tier's log lines (PKT-640: a TLS handshake a peer failed or
; abandoned is named in the service log, not only on stderr).

(defun fn-cbud-kib (octets)
  (declare (xargs :guard t))
  (floor (+ (nfix octets) 1023) 1024))

(defun fn-cbud-refusal-line (decision article tlsp machine)
  (declare (xargs :guard t))
  (concatenate 'string
               "refused connections-exceed-memory capacity="
               (fn-heap-decimal (nth 2 (true-list-fix decision)))
               " holds=" (fn-heap-decimal (nth 3 (true-list-fix decision)))
               " per-connection=" (fn-heap-decimal
                                   (fn-cbud-kib (fn-cbud-conn-octets article tlsp)))
               " KiB machine=" (fn-heap-decimal (floor (nfix machine) *fn-heap-mib*))
               " MB"))

(defun fn-cbud-hold-line (decision article tlsp)
  (declare (xargs :guard t))
  (concatenate 'string
               "connections holds=" (fn-heap-decimal (fn-cbud-held-bound decision))
               " per-connection=" (fn-heap-decimal
                                   (fn-cbud-kib (fn-cbud-conn-octets article tlsp)))
               " KiB"))

(defconst *fn-cbud-tls-reasons*
  '((:handshake . "handshake") (:timeout . "timeout") (:closed . "closed")
    (:refused . "refused") (:busy . "busy")))

(defun fn-cbud-tls-refusal-line (reason id)
  (declare (xargs :guard t))
  (let ((word (cdr (assoc-equal reason *fn-cbud-tls-reasons*))))
    (concatenate 'string "tls refused reason=" (if (stringp word) word "other")
                 " connection=" (fn-heap-decimal id))))

; -----------------------------------------------------------------------------
; The bound: the most connections the machine holds beside the base.  Every
; part of every connection is memory of the machine (the heap part also
; lives in the dynamic space: see the header on what the figure holds).

(defun fn-cbud-machine-room (machine hneed core threads stack hs)
  (declare (xargs :guard t))
  (nfix (- (nfix machine) (fn-cbud-base-octets hneed core threads stack hs))))

(defun fn-cbud-div (room per)
  (declare (xargs :guard t))
  (if (and (natp room) (posp per)) (floor room per) 0))

(local (include-book "arithmetic-5/top" :dir :system))

(defthm fn-cbud-div-natp
  (natp (fn-cbud-div room per))
  :rule-classes :type-prescription)

(defthm fn-cbud-div-fits
  (implies (and (natp room) (posp per) (natp n) (<= n (fn-cbud-div room per)))
           (<= (* n per) room))
  :hints (("Goal" :nonlinearp t)))

(defthm fn-cbud-div-is-the-most
  (implies (and (natp room) (posp per))
           (< room (* (+ 1 (fn-cbud-div room per)) per)))
  :hints (("Goal" :nonlinearp t)))

(in-theory (disable fn-cbud-div))

(defun fn-cbud-bound (machine hneed core threads stack hs article tlsp)
  (declare (xargs :guard t))
  (fn-cbud-div (fn-cbud-machine-room machine hneed core threads stack hs)
               (fn-cbud-conn-octets article tlsp)))

(defthm fn-cbud-bound-natp
  (natp (fn-cbud-bound machine hneed core threads stack hs article tlsp))
  :rule-classes :type-prescription)

; KEYSTONE (PRF-223).  Every count of connections up to the bound fits: the
; base (the store's heap figure, the core, the fixed threads) and that many
; connections at the per-connection figure are within the machine.
(defthm fn-cbud-bound-holds-its-connections
  (implies (and (<= (nfix n)
                    (fn-cbud-bound machine hneed core threads stack hs article tlsp))
                (<= (fn-cbud-base-octets hneed core threads stack hs) (nfix machine)))
           (<= (+ (fn-cbud-base-octets hneed core threads stack hs)
                  (* (nfix n) (fn-cbud-conn-octets article tlsp)))
               (nfix machine)))
  :hints (("Goal"
           :in-theory (e/d (fn-cbud-machine-room)
                           (fn-cbud-conn-octets fn-cbud-base-octets))
           :use ((:instance fn-cbud-div-fits
                            (n (nfix n))
                            (room (fn-cbud-machine-room machine hneed core threads stack hs))
                            (per (fn-cbud-conn-octets article tlsp)))))))

; The bound is the most: one connection past it does not fit.
(defthm fn-cbud-bound-is-the-most
  (< (nfix machine)
     (+ (fn-cbud-base-octets hneed core threads stack hs)
        (* (+ 1 (fn-cbud-bound machine hneed core threads stack hs article tlsp))
           (fn-cbud-conn-octets article tlsp))))
  :hints (("Goal"
           :in-theory (e/d (fn-cbud-machine-room)
                           (fn-cbud-conn-octets fn-cbud-base-octets))
           :cases ((<= (fn-cbud-base-octets hneed core threads stack hs) (nfix machine)))
           :use ((:instance fn-cbud-div-is-the-most
                            (room (fn-cbud-machine-room machine hneed core threads stack hs))
                            (per (fn-cbud-conn-octets article tlsp))))))
  :rule-classes nil)

(in-theory (disable fn-cbud-bound))

; -----------------------------------------------------------------------------
; The dynamic space caps the heap.  SBCL never maps more heap than the
; DYNAMIC space the process was started with, so the resident heap is at
; most the lesser of DYNAMIC and the store's figure plus the connections'
; heap parts; past DYNAMIC the process meets heap exhaustion (a fault, exit
; 4), never the machine.  The resident figure of n connections:

(defun fn-cbud-resident-octets (dynamic hneed core threads stack hs article tlsp n)
  (declare (xargs :guard t))
  (+ (min (nfix dynamic)
          (+ (nfix hneed) (* (nfix n) (fn-cbud-conn-heap-octets article))))
     (fn-cbud-rest-octets core threads stack hs)
     (* (nfix n) (fn-cbud-conn-native-octets tlsp))))

; Two ways the machine holds n connections: the store's figure and every
; part of each (the bound above: the launcher's case, where DYNAMIC is the
; figure plus room), or the whole dynamic space and each one's native part
; (a dynamic space below the machine that the store's worst case exceeds).
(defun fn-cbud-fits-figure (machine hneed core threads stack hs)
  (declare (xargs :guard t))
  (<= (fn-cbud-base-octets hneed core threads stack hs) (nfix machine)))

(defun fn-cbud-fits-dynamic (machine dynamic core threads stack hs)
  (declare (xargs :guard t))
  (<= (+ (nfix dynamic) (fn-cbud-rest-octets core threads stack hs)) (nfix machine)))

(defun fn-cbud-capped-bound (machine dynamic core threads stack hs tlsp)
  (declare (xargs :guard t))
  (fn-cbud-div (nfix (- (nfix machine)
                        (+ (nfix dynamic) (fn-cbud-rest-octets core threads stack hs))))
               (fn-cbud-conn-native-octets tlsp)))

; The most connections the process holds within the machine.
(defun fn-cbud-limit (machine dynamic hneed core threads stack hs article tlsp)
  (declare (xargs :guard t))
  (max (if (fn-cbud-fits-figure machine hneed core threads stack hs)
           (fn-cbud-bound machine hneed core threads stack hs article tlsp)
         0)
       (if (fn-cbud-fits-dynamic machine dynamic core threads stack hs)
           (fn-cbud-capped-bound machine dynamic core threads stack hs tlsp)
         0)))

(defun fn-cbud-base-fitsp (machine dynamic hneed core threads stack hs)
  (declare (xargs :guard t))
  (or (fn-cbud-fits-figure machine hneed core threads stack hs)
      (fn-cbud-fits-dynamic machine dynamic core threads stack hs)))

; The run's refusal as the owner prints it (host/owner-host.lisp
; fn-owner-connection-budget).  When the base itself does not fit (holds=0
; whatever the capacity), the line names the parts, so a node started under
; a memory limit that its dynamic space and its store's heap figure both
; exceed says so instead of blaming the connections: `base-exceeds-machine
; heap-figure=F MB dynamic=D MB fixed=R MB'.  bin/fn sizes the dynamic space
; from the store; a raw image keeps its build's size (lane ops-fixes: three
; lanes read `holds=0' as a silent or unexplained start failure).
(defun fn-cbud-mb-up (octets)
  (declare (xargs :guard t))
  (floor (+ (nfix octets) (- *fn-heap-mib* 1)) *fn-heap-mib*))

(defthm fn-cbud-mb-up-natp
  (natp (fn-cbud-mb-up octets))
  :rule-classes :type-prescription)

(defun fn-cbud-base-line (dynamic hneed core threads stack hs)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-cbud-mb-up
                                                            fn-cbud-rest-octets)))))
  (concatenate 'string
               " base-exceeds-machine heap-figure=" (fn-heap-decimal (fn-cbud-mb-up hneed))
               " MB dynamic=" (fn-heap-decimal (fn-cbud-mb-up dynamic))
               " MB fixed=" (fn-heap-decimal
                             (fn-cbud-mb-up (fn-cbud-rest-octets core threads stack hs)))
               " MB"))

(defun fn-cbud-run-refusal-line (decision article tlsp machine dynamic hneed core
                                          threads stack hs)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-cbud-base-fitsp
                                                            fn-cbud-refusal-line
                                                            fn-cbud-base-line)))))
  (if (fn-cbud-base-fitsp machine dynamic hneed core threads stack hs)
      (fn-cbud-refusal-line decision article tlsp machine)
    (concatenate 'string
                 (fn-cbud-refusal-line decision article tlsp machine)
                 (fn-cbud-base-line dynamic hneed core threads stack hs))))

(defthm fn-cbud-limit-natp
  (natp (fn-cbud-limit machine dynamic hneed core threads stack hs article tlsp))
  :rule-classes :type-prescription)

(defthm fn-cbud-rest-octets-natp
  (natp (fn-cbud-rest-octets core threads stack hs))
  :rule-classes :type-prescription)

(defthm fn-cbud-base-is-the-figure-and-the-rest
  (equal (fn-cbud-base-octets hneed core threads stack hs)
         (+ (nfix hneed) (fn-cbud-rest-octets core threads stack hs))))

(defthm fn-cbud-conn-octets-is-the-parts
  (equal (fn-cbud-conn-octets article tlsp)
         (+ (fn-cbud-conn-heap-octets article) (fn-cbud-conn-native-octets tlsp))))

(in-theory (disable fn-cbud-base-octets fn-cbud-rest-octets fn-cbud-conn-octets
                    fn-cbud-conn-heap-octets fn-cbud-conn-native-octets))

(local
 (defthm fn-cbud-resident-within-the-figure
   (<= (fn-cbud-resident-octets dynamic hneed core threads stack hs article tlsp n)
       (+ (fn-cbud-base-octets hneed core threads stack hs)
          (* (nfix n) (fn-cbud-conn-octets article tlsp))))))

(local
 (defthm fn-cbud-resident-within-the-dynamic-space
   (<= (fn-cbud-resident-octets dynamic hneed core threads stack hs article tlsp n)
       (+ (nfix dynamic) (fn-cbud-rest-octets core threads stack hs)
          (* (nfix n) (fn-cbud-conn-native-octets tlsp))))))

(in-theory (disable fn-cbud-resident-octets))

(local
 (defthm fn-cbud-held-by-the-figure
   (implies (and (fn-cbud-fits-figure machine hneed core threads stack hs)
                 (<= (nfix n) (fn-cbud-bound machine hneed core threads stack hs
                                             article tlsp)))
            (<= (fn-cbud-resident-octets dynamic hneed core threads stack hs article tlsp n)
                (nfix machine)))
   :hints (("Goal" :in-theory (disable fn-cbud-resident-within-the-figure)
            :use ((:instance fn-cbud-resident-within-the-figure)
                  (:instance fn-cbud-bound-holds-its-connections))))))

(local
 (defthm fn-cbud-held-by-the-dynamic-space
   (implies (and (fn-cbud-fits-dynamic machine dynamic core threads stack hs)
                 (<= (nfix n) (fn-cbud-capped-bound machine dynamic core threads
                                                    stack hs tlsp)))
            (<= (fn-cbud-resident-octets dynamic hneed core threads stack hs article tlsp n)
                (nfix machine)))
   :hints (("Goal" :in-theory (disable fn-cbud-resident-within-the-dynamic-space)
            :use ((:instance fn-cbud-resident-within-the-dynamic-space)
                  (:instance fn-cbud-div-fits
                             (n (nfix n))
                             (room (nfix (- (nfix machine)
                                            (+ (nfix dynamic)
                                               (fn-cbud-rest-octets core threads stack hs)))))
                             (per (fn-cbud-conn-native-octets tlsp))))))))

; KEYSTONE (PRF-223).  Every count of connections up to the limit is held:
; the resident figure of that many is within the machine.
(defthm fn-cbud-limit-holds-its-connections
  (implies (and (<= (nfix n)
                    (fn-cbud-limit machine dynamic hneed core threads stack hs article tlsp))
                (fn-cbud-base-fitsp machine dynamic hneed core threads stack hs))
           (<= (fn-cbud-resident-octets dynamic hneed core threads stack hs article tlsp n)
               (nfix machine)))
  :hints (("Goal" :in-theory (e/d (fn-cbud-limit)
                                  (fn-cbud-fits-figure fn-cbud-fits-dynamic
                                   fn-cbud-capped-bound fn-cbud-bound
                                   fn-cbud-held-by-the-figure
                                   fn-cbud-held-by-the-dynamic-space))
           :use ((:instance fn-cbud-held-by-the-figure)
                 (:instance fn-cbud-held-by-the-dynamic-space)
                 (:instance fn-cbud-held-by-the-figure (n 0))
                 (:instance fn-cbud-held-by-the-dynamic-space (n 0))))))

(local
 (defthm fn-cbud-resident-above-when-both-exceed
   (implies (and (< (nfix machine)
                    (+ (fn-cbud-base-octets hneed core threads stack hs)
                       (* (nfix n) (fn-cbud-conn-octets article tlsp))))
                 (< (nfix machine)
                    (+ (nfix dynamic) (fn-cbud-rest-octets core threads stack hs)
                       (* (nfix n) (fn-cbud-conn-native-octets tlsp)))))
            (< (nfix machine)
               (fn-cbud-resident-octets dynamic hneed core threads stack hs article tlsp n)))
   :hints (("Goal" :in-theory (enable fn-cbud-resident-octets)))))

(local
 (defthm fn-cbud-more-still-exceeds
   (implies (and (< m (+ a (* k f))) (<= k j) (natp f) (rationalp a)
                 (rationalp m) (natp k) (natp j))
            (< m (+ a (* j f))))
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm fn-cbud-limit-at-least-the-figure-bound
   (implies (fn-cbud-fits-figure machine hneed core threads stack hs)
            (<= (fn-cbud-bound machine hneed core threads stack hs article tlsp)
                (fn-cbud-limit machine dynamic hneed core threads stack hs article tlsp)))
   :hints (("Goal" :in-theory (e/d (fn-cbud-limit)
                                   (fn-cbud-bound fn-cbud-capped-bound
                                    fn-cbud-fits-figure fn-cbud-fits-dynamic))))))

(local
 (defthm fn-cbud-limit-at-least-the-capped-bound
   (implies (fn-cbud-fits-dynamic machine dynamic core threads stack hs)
            (<= (fn-cbud-capped-bound machine dynamic core threads stack hs tlsp)
                (fn-cbud-limit machine dynamic hneed core threads stack hs article tlsp)))
   :hints (("Goal" :in-theory (e/d (fn-cbud-limit)
                                   (fn-cbud-bound fn-cbud-capped-bound
                                    fn-cbud-fits-figure fn-cbud-fits-dynamic))))))

(local
 (defthm fn-cbud-past-the-limit-exceeds-the-figure
   (let ((l (fn-cbud-limit machine dynamic hneed core threads stack hs article tlsp)))
     (< (nfix machine)
        (+ (fn-cbud-base-octets hneed core threads stack hs)
           (* (+ 1 l) (fn-cbud-conn-octets article tlsp)))))
   :hints (("Goal"
            :in-theory (e/d (fn-cbud-fits-figure)
                            (fn-cbud-more-still-exceeds
                             fn-cbud-limit-at-least-the-figure-bound))
            :cases ((fn-cbud-fits-figure machine hneed core threads stack hs))
            :use ((:instance fn-cbud-bound-is-the-most)
                  (:instance fn-cbud-limit-at-least-the-figure-bound)
                  (:instance fn-cbud-more-still-exceeds
                             (m (nfix machine))
                             (a (fn-cbud-base-octets hneed core threads stack hs))
                             (f (fn-cbud-conn-octets article tlsp))
                             (k (+ 1 (fn-cbud-bound machine hneed core threads stack hs
                                                    article tlsp)))
                             (j (+ 1 (fn-cbud-limit machine dynamic hneed core threads
                                                    stack hs article tlsp)))))))))

(local
 (defthm fn-cbud-past-the-limit-exceeds-the-dynamic-space
   (let ((l (fn-cbud-limit machine dynamic hneed core threads stack hs article tlsp)))
     (< (nfix machine)
        (+ (nfix dynamic) (fn-cbud-rest-octets core threads stack hs)
           (* (+ 1 l) (fn-cbud-conn-native-octets tlsp)))))
   :hints (("Goal"
            :in-theory (e/d (fn-cbud-fits-dynamic fn-cbud-capped-bound)
                            (fn-cbud-more-still-exceeds
                             fn-cbud-limit-at-least-the-capped-bound))
            :cases ((fn-cbud-fits-dynamic machine dynamic core threads stack hs))
            :use ((:instance fn-cbud-div-is-the-most
                             (room (nfix (- (nfix machine)
                                            (+ (nfix dynamic)
                                               (fn-cbud-rest-octets core threads stack hs)))))
                             (per (fn-cbud-conn-native-octets tlsp)))
                  (:instance fn-cbud-limit-at-least-the-capped-bound)
                  (:instance fn-cbud-more-still-exceeds
                             (m (nfix machine))
                             (a (+ (nfix dynamic) (fn-cbud-rest-octets core threads stack hs)))
                             (f (fn-cbud-conn-native-octets tlsp))
                             (k (+ 1 (fn-cbud-capped-bound machine dynamic core threads
                                                           stack hs tlsp)))
                             (j (+ 1 (fn-cbud-limit machine dynamic hneed core threads
                                                    stack hs article tlsp)))))))))

; The limit is the most: one connection past it is not held.
(defthm fn-cbud-limit-is-the-most
  (< (nfix machine)
     (fn-cbud-resident-octets dynamic hneed core threads stack hs article tlsp
                              (+ 1 (fn-cbud-limit machine dynamic hneed core threads
                                                  stack hs article tlsp))))
  :hints (("Goal"
           :in-theory (disable fn-cbud-resident-above-when-both-exceed
                               fn-cbud-past-the-limit-exceeds-the-figure
                               fn-cbud-past-the-limit-exceeds-the-dynamic-space
                               fn-cbud-limit fn-cbud-base-octets
                               fn-cbud-rest-octets)
           :use ((:instance fn-cbud-resident-above-when-both-exceed
                            (n (+ 1 (fn-cbud-limit machine dynamic hneed core threads
                                                   stack hs article tlsp))))
                 (:instance fn-cbud-past-the-limit-exceeds-the-figure)
                 (:instance fn-cbud-past-the-limit-exceeds-the-dynamic-space))))
  :rule-classes nil)

(in-theory (disable fn-cbud-limit))

; -----------------------------------------------------------------------------
; The launcher's room.  Before lane zero-copy-commit `fn-cbud-launch-decide'
; added room for up to 1,024 connections' heap parts to heap-figure's figure;
; no host line had called it since lane reservation-figure.  It is gone: the
; figure itself holds the one per-connection heap term that grows with the
; profile, the articles in flight (books/heap-store-figure.lisp
; fn-heap-articles-octets), and the rest of a connection's heap part is
; charged to the machine here.

; -----------------------------------------------------------------------------
; The run's decision.  CAPACITY is the live configuration's
; (`fn-exp-connections-capacity'), the rest the host's observations and the
; store's profile.  Answers (:hold B) or (:refused :connections-exceed-memory
; CAPACITY B).

(defun fn-cbud-run-decide (capacity machine dynamic hneed core threads stack hs article tlsp)
  (declare (xargs :guard t))
  (let ((b (fn-cbud-limit machine dynamic hneed core threads stack hs article tlsp)))
    (if (and (<= (nfix capacity) b)
             (fn-cbud-base-fitsp machine dynamic hneed core threads stack hs))
        (list :hold b)
      (list :refused :connections-exceed-memory (nfix capacity) b))))

; KEYSTONE (PRF-223).  An accepted run holds its capacity: the capacity is
; within the limit, and the resident figure of that many connections is
; within the machine.
(defthm fn-cbud-run-decide-holds-the-capacity
  (let ((d (fn-cbud-run-decide capacity machine dynamic hneed core threads stack hs
                               article tlsp)))
    (implies (equal (car d) :hold)
             (and (<= (nfix capacity) (fn-cbud-held-bound d))
                  (equal (fn-cbud-held-bound d)
                         (fn-cbud-limit machine dynamic hneed core threads stack hs
                                        article tlsp))
                  (<= (fn-cbud-resident-octets dynamic hneed core threads stack hs article
                                               tlsp capacity)
                      (nfix machine)))))
  :hints (("Goal" :in-theory (disable fn-cbud-base-fitsp)
           :use ((:instance fn-cbud-limit-holds-its-connections
                            (n capacity))))))

(defthm fn-cbud-run-decide-refuses-exactly-past-the-limit
  (equal (equal (car (fn-cbud-run-decide capacity machine dynamic hneed core threads
                                         stack hs article tlsp))
                :refused)
         (or (< (fn-cbud-limit machine dynamic hneed core threads stack hs article tlsp)
                (nfix capacity))
             (not (fn-cbud-base-fitsp machine dynamic hneed core threads stack hs))))
  :hints (("Goal" :in-theory (disable fn-cbud-base-fitsp))))

; -----------------------------------------------------------------------------
; Admission under an accepted capacity.  The maintained relation is: the live
; capacity is at most the limit the run held (established by the run's
; decision, `fn-owner-connection-budget'; preserved by every live
; reconfiguration, which `fn-cbud-deltas-refusal' below refuses past it).
; With PRF-211's keystone an admitted connection is one of fewer than the
; capacity, so the set it joins, trusted sources included, is held.

(defthm fn-cbud-admitted-connections-fit-the-machine
  (let ((lim (fn-exp-limits v *fn-exp-owner-connection-bound* publicp
                            auth-required)))
    (implies (and (fn-cfg-limits-withinp (fn-cfg-limits v))
                  (not (fn-exp-auth-refusesp xs lim address now))
                  (equal (fn-exp-admit-decision xs lim nconns address now)
                         (list :admit))
                  (<= (fn-exp-connections-capacity v)
                      (fn-cbud-limit machine dynamic hneed core threads stack hs article tlsp))
                  (fn-cbud-base-fitsp machine dynamic hneed core threads stack hs))
             (<= (fn-cbud-resident-octets dynamic hneed core threads stack hs article tlsp
                                          (+ 1 (nfix nconns)))
                 (nfix machine))))
  :hints (("Goal" :in-theory (disable fn-cbud-base-fitsp
                                      fn-exp-admit-decision fn-exp-limits
                                      fn-exp-connections-capacity
                                      fn-exp-auth-refusesp
                                      fn-cfg-limits-withinp
                                      fn-exp-trusted-addressp fn-exp-count-address)
           :use ((:instance fn-exp-open-refuses-exactly-at-the-capacity)
                 (:instance fn-cbud-limit-holds-its-connections
                            (n (+ 1 (nfix nconns))))))))

; -----------------------------------------------------------------------------
; A live reconfiguration.  HELD is what the run's accepted decision held
; (fn-cbud-run-held: its observations and the handshake slots it charged),
; or NIL for an owner no run installed one in (the ACL2 test entries; every
; served run installs it before LISTENING, host/native/owner.lisp
; fnn-owner-run).  The configuration the deltas make is decided again, on
; the run's observations: its capacity, and the handshake slots the larger
; of the held ones and its own `tls-handshakes-in-flight' (lowering L never
; frees the charge while the run lives: the handshakes admitted under the
; old L may still be in flight).  Past the machine it is refused by name:
; :handshakes-exceed-memory when the capacity alone holds under the held
; slots, :connections-exceed-memory otherwise.

(defun fn-cbud-slots-octets (slots)
  (declare (xargs :guard t))
  (* (nfix slots) *fn-cbud-handshake-scratch-octets*))

(defthm fn-cbud-handshake-octets-is-the-slots
  (equal (fn-cbud-handshake-octets tlsp inflight)
         (fn-cbud-slots-octets (fn-cbud-handshake-slots tlsp inflight))))

(defun fn-cbud-run-held (machine dynamic hneed core threads stack article tlsp slots)
  (declare (xargs :guard t))
  (list machine dynamic hneed core threads stack article tlsp (nfix slots)))

(defun fn-cbud-held-at (i held)
  (declare (xargs :guard t))
  (if (natp i) (nth i (true-list-fix held)) nil))

(defun fn-cbud-deltas-capacity (v gen stamp deltas)
  (declare (xargs :guard t))
  (fn-exp-connections-capacity (fn-cfg-apply v gen stamp deltas)))

(defun fn-cbud-deltas-slots (v gen stamp deltas held)
  (declare (xargs :guard t))
  (max (nfix (fn-cbud-held-at 8 held))
       (nfix (fn-cbud-config-handshake-slots (fn-cfg-apply v gen stamp deltas)
                                             (fn-cbud-held-at 7 held)))))

(defun fn-cbud-held-decide (capacity slots held)
  (declare (xargs :guard t))
  (fn-cbud-run-decide capacity
                      (fn-cbud-held-at 0 held) (fn-cbud-held-at 1 held)
                      (fn-cbud-held-at 2 held) (fn-cbud-held-at 3 held)
                      (fn-cbud-held-at 4 held) (fn-cbud-held-at 5 held)
                      (fn-cbud-slots-octets slots)
                      (fn-cbud-held-at 6 held) (fn-cbud-held-at 7 held)))

(defun fn-cbud-deltas-refusal (v gen stamp deltas held)
  (declare (xargs :guard t))
  (let ((capacity (fn-cbud-deltas-capacity v gen stamp deltas)))
    (cond ((not (consp held)) nil)
          ((equal (car (fn-cbud-held-decide
                        capacity (fn-cbud-deltas-slots v gen stamp deltas held) held))
                  :hold)
           nil)
          ((equal (car (fn-cbud-held-decide
                        capacity (nfix (fn-cbud-held-at 8 held)) held))
                  :hold)
           :handshakes-exceed-memory)
          (t :connections-exceed-memory))))

; What the owner holds after a delta list it did not refuse: the slots the
; new configuration was decided with.  (Taken at the check, before the
; staging's durable write: a staging that then fails leaves a charge at
; most larger than needed, never smaller.)
(defun fn-cbud-deltas-held (v gen stamp deltas held)
  (declare (xargs :guard t))
  (if (consp held)
      (fn-cbud-run-held (fn-cbud-held-at 0 held) (fn-cbud-held-at 1 held)
                        (fn-cbud-held-at 2 held) (fn-cbud-held-at 3 held)
                        (fn-cbud-held-at 4 held) (fn-cbud-held-at 5 held)
                        (fn-cbud-held-at 6 held) (fn-cbud-held-at 7 held)
                        (fn-cbud-deltas-slots v gen stamp deltas held))
    held))

; KEYSTONE (PRF-223, with PRF-986's term).  A live reconfiguration the owner
; stages keeps the process within the machine: the new configuration's
; capacity of connections, with the handshake scratch of the slots it
; holds, is within the run's machine, on the run's observations.
(defthm fn-cbud-deltas-refusal-keeps-the-machine-held
  (let ((held2 (fn-cbud-deltas-held v gen stamp deltas held)))
    (implies (and (consp held)
                  (not (fn-cbud-deltas-refusal v gen stamp deltas held)))
             (and (<= (fn-exp-connections-capacity (fn-cfg-apply v gen stamp deltas))
                      (fn-cbud-limit (fn-cbud-held-at 0 held2) (fn-cbud-held-at 1 held2)
                                     (fn-cbud-held-at 2 held2) (fn-cbud-held-at 3 held2)
                                     (fn-cbud-held-at 4 held2) (fn-cbud-held-at 5 held2)
                                     (fn-cbud-slots-octets (fn-cbud-held-at 8 held2))
                                     (fn-cbud-held-at 6 held2) (fn-cbud-held-at 7 held2)))
                  (<= (fn-cbud-resident-octets
                       (fn-cbud-held-at 1 held2) (fn-cbud-held-at 2 held2)
                       (fn-cbud-held-at 3 held2) (fn-cbud-held-at 4 held2)
                       (fn-cbud-held-at 5 held2)
                       (fn-cbud-slots-octets (fn-cbud-held-at 8 held2))
                       (fn-cbud-held-at 6 held2) (fn-cbud-held-at 7 held2)
                       (fn-exp-connections-capacity (fn-cfg-apply v gen stamp deltas)))
                      (nfix (fn-cbud-held-at 0 held2)))
                  (<= (nfix (fn-cbud-config-handshake-slots (fn-cfg-apply v gen stamp deltas)
                                                            (fn-cbud-held-at 7 held2)))
                      (fn-cbud-held-at 8 held2))
                  (<= (nfix (fn-cbud-held-at 8 held)) (fn-cbud-held-at 8 held2)))))
  :hints (("Goal" :in-theory (disable fn-cbud-run-decide fn-cbud-limit
                                      fn-cbud-resident-octets fn-cbud-config-handshake-slots
                                      fn-exp-connections-capacity fn-cfg-apply)
           :use ((:instance fn-cbud-run-decide-holds-the-capacity
                            (capacity (fn-cbud-deltas-capacity v gen stamp deltas))
                            (machine (fn-cbud-held-at 0 held))
                            (dynamic (fn-cbud-held-at 1 held))
                            (hneed (fn-cbud-held-at 2 held))
                            (core (fn-cbud-held-at 3 held))
                            (threads (fn-cbud-held-at 4 held))
                            (stack (fn-cbud-held-at 5 held))
                            (hs (fn-cbud-slots-octets
                                 (fn-cbud-deltas-slots v gen stamp deltas held)))
                            (article (fn-cbud-held-at 6 held))
                            (tlsp (fn-cbud-held-at 7 held)))))))
