; Input and private command buffers for a TLS NNTP client.
(in-package "ACL2")
(include-book "authinfo-secret-pool")
(include-book "pool-ranges")
(include-book "pool-zero")
(fn2-book-layer :e)

; The framing primitive verified LF and capped the line. Check the exact
; status separator and the complete UTF-8/CRLF line before trusting its code.
(defun fn2-peer-pull-line (start pos slot gen kind owner generation fn2-pool)
 (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)
                 :guard-hints (("Goal" :in-theory (disable fn2-gram-frame)))))
 (b* (((mv status begin next &)
       (fn2-gram-frame *fn2-nntp-line-cap* (nfix start) (max (nfix start) (nfix pos)) 0
                       *fn2-nntp-line-cap* slot gen kind owner generation fn2-pool))
      ((unless (unsigned-byte-p 32 next)) (mv :frame 0 0))
      ((unless (eq status :line)) (mv status next 0))
      ((unless (and (natp begin) (<= (+ begin 5) next)))
       (mv :frame next 0))
      ((mv cr-ok cr) (fn2-gram-read slot gen (- next 2) kind owner generation fn2-pool))
      ((mv bad ctl need) (fn2-gram-line-scan (- next (+ 2 begin)) begin 0 #x80 #xbf nil nil slot gen kind owner generation fn2-pool))
      ((unless (and cr-ok (equal cr 13) (not bad) (not ctl) (equal need 0))) (mv :frame next 0))
      ((mv valid code) (fn2-gram-digits 3 begin 0 slot gen kind owner generation fn2-pool))
      ((mv ok separator) (fn2-gram-read slot gen (+ 3 begin) kind owner generation fn2-pool)))
   (if (and valid (unsigned-byte-p 16 code) ok
            (if (equal next (+ begin 5)) (equal separator 13) (equal separator 32)))
       (mv :ok next code)
     (mv :frame next 0))))
(defthm fn2-peer-pull-line-widths
 (and (unsigned-byte-p 32 (mv-nth 1 (fn2-peer-pull-line start pos slot gen kind owner generation fn2-pool)))
      (unsigned-byte-p 16 (mv-nth 2 (fn2-peer-pull-line start pos slot gen kind owner generation fn2-pool))))
 :hints (("Goal" :in-theory (disable fn2-gram-frame))))
(in-theory (disable fn2-peer-pull-line))

(defun fn2-peer-pull-copy-credentials (src sgen source-kind source source-gen stream-off stream-len user-off user-len pass-off pass-len
                                       dest dgen kind owner generation fn2-pool)
 (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
 (b* (((unless (and (not (equal src dest)) (natp stream-off) (posp stream-len) (<= stream-len 64)
                    (fn2-authinfo-token-span-p src sgen stream-off stream-len source-kind source source-gen fn2-pool)
                    (fn2-authinfo-token-span-p src sgen user-off user-len source-kind source source-gen fn2-pool)
                    (fn2-authinfo-token-span-p src sgen pass-off pass-len source-kind source source-gen fn2-pool)
                    (natp user-off) (natp pass-off) (posp user-len) (posp pass-len)
                    (<= (+ stream-off stream-len) user-off) (<= (+ user-off user-len) pass-off)
                    (eq (fn2-pool-workspace-code dest dgen kind owner generation fn2-pool) :ok)
                    (zp (fn2-pool-fill-value dest fn2-pool))))
       (mv :frame fn2-pool))
      ((mv code fn2-pool) (fn2-rd-copy stream-len src sgen stream-off source-kind source source-gen
                                     dest dgen 0 kind owner generation fn2-pool))
      ((unless (eq code :ok)) (mv :capacity fn2-pool))
      ((mv code fn2-pool) (fn2-rd-copy user-len src sgen user-off source-kind source source-gen
                                     dest dgen stream-len kind owner generation fn2-pool))
      ((unless (eq code :ok)) (mv :capacity fn2-pool))
      ((mv code fn2-pool) (fn2-rd-copy pass-len src sgen pass-off source-kind source source-gen
                                     dest dgen (+ stream-len user-len) kind owner generation fn2-pool)))
   (mv (if (eq code :ok) :ok :capacity) fn2-pool)))
(fn2-pool-preserves fn2-peer-pull-copy-credentials
 (src sgen source-kind source source-gen stream-off stream-len user-off user-len pass-off pass-len dest dgen kind owner generation fn2-pool)
 :position 1 :rows nil)
(in-theory (disable fn2-peer-pull-copy-credentials))

(defun fn2-peer-pull-format-command (command protected secret sgen stream-len user-len pass-len tx tgen kind owner generation fn2-pool)
 (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)
                 :guard-hints (("Goal" :in-theory (disable fn2-pool-write fn2-pool-workspace-code)))))
 (b* (((unless (or (eq command :starttls) (and (equal protected 1) (member-eq command '(:user :pass)))))
       (mv :access fn2-pool))
      ((unless (and (not (equal secret tx))
                    (eq (fn2-pool-workspace-code tx tgen kind owner generation fn2-pool) :ok)
                    (zp (fn2-pool-fill-value tx fn2-pool))))
       (mv :state fn2-pool))
      (prefix (case command (:starttls "STARTTLS") (:user "AUTHINFO USER ") (otherwise "AUTHINFO PASS ")))
      ((mv code fn2-pool) (fn2-pool-append-text 0 prefix tx tgen kind owner generation fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-pool))
      (len (case command (:user (nfix user-len)) (:pass (nfix pass-len)) (otherwise 0)))
      ((unless (or (eq command :starttls) (and (posp len) (<= len *fn2-authinfo-pass-max*))))
       (mv :bounds fn2-pool))
      ((mv code fn2-pool) (fn2-rd-copy len secret sgen (+ (nfix stream-len) (if (eq command :pass) (nfix user-len) 0))
                                      kind owner generation tx tgen (length prefix) kind owner generation fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-pool))
      (end (+ (length prefix) len))
      ((mv code fn2-pool) (fn2-pool-write tx tgen end 13 kind owner generation fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-pool)))
   (fn2-pool-write tx tgen (+ 1 end) 10 kind owner generation fn2-pool)))
(fn2-pool-preserves fn2-peer-pull-format-command
 (command protected secret sgen stream-len user-len pass-len tx tgen kind owner generation fn2-pool) :position 1 :rows nil
 :hints (("Goal" :in-theory (disable fn2-pool-write fn2-pool-workspace-code))))
(in-theory (disable fn2-peer-pull-format-command))

; Executed after the terminal returned the loan. Truncation alone leaves
; the former password octets resident in the underlying pool array.
(defun fn2-peer-pull-wipe (slot gen keep bound kind owner generation fn2-pool)
 (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
 (b* ((len (fn2-pool-fill-value slot fn2-pool))
      ((unless (and (natp len) (natp keep) (<= keep len) (natp bound) (<= len bound) (<= bound (+ 250 (* 2 *fn2-nntp-line-cap*)))))
       (mv :bounds fn2-pool))
      ((mv code fn2-pool) (fn2-run-zero (- len keep) slot gen keep kind owner generation fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-pool)))
   (fn2-pool-truncate slot gen keep kind owner generation fn2-pool)))
(fn2-pool-preserves fn2-peer-pull-wipe (slot gen keep bound kind owner generation fn2-pool) :position 1 :rows nil)
(in-theory (disable fn2-peer-pull-wipe))
