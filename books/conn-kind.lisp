;; Schema and partition registration for fn2-conn (layer D, quest D3).
;; Arm bodies and helper operations live in books/conn.lisp (a leaf book).
(in-package "ACL2")
(include-book "machines-a")
(include-book "profile")
(include-book "conn-answer")
(include-book "tls-kind")
(include-book "accounts-core")
(include-book "upload-scan")
(include-book "upload-feed")
(include-book "machine-arms") ; defmachine-registry (MACHINE-FORM 6.5 P4)
(fn2-book-layer :d)

; Shared by connection and upload continuations; declare once before either leaf.
(defcost fn2-conn-wake :tables (fn2-core-machines)
 :doc "Wake the upload or cursor this connection serves.")

;; The run quantum, split statically (section 4.2): the framer examines at
;; most *fn2-conn-frame-bytes*; a framed line costs at most
;; *fn2-conn-answer-bytes* (re-read 512, status 512, fixed body 1,024); a
;; run that needs input compacts at most *fn2-conn-compact-bytes* and
;; receives at most *fn2-conn-receive-bytes*.
(defconst *fn2-conn-frame-bytes* 2048)
(defconst *fn2-conn-answer-bytes* (+ 512 512 *fn2-answer-body-bytes*))
(defconst *fn2-conn-compact-bytes* 1024)
(defconst *fn2-conn-receive-bytes* 1024)
(defconst *fn2-conn-send-bytes* 4096)
(defconst *fn2-conn-run-bytes* (+ *fn2-conn-frame-bytes* *fn2-conn-answer-bytes*))
(defconst *fn2-conn-input-bytes* (+ *fn2-conn-frame-bytes* *fn2-conn-compact-bytes* *fn2-conn-receive-bytes*))
(defconst *fn2-conn-range-min* 1024)
;; Article input (section 14.2): at most this many RX octets fed per run
;; (each read once and written at most once).
(defconst *fn2-conn-feed-bytes* 1024)
(defconst *fn2-conn-feed-cost* (* 2 *fn2-conn-feed-bytes*))
;; The feed's mode after the terminator (upload-feed.lisp uses 0..4).
(defconst *fn2-conn-feed-done* 5)
(assert-event (and (equal *fn2-conn-run-bytes* 4096) (equal *fn2-conn-input-bytes* 4096)
                   (<= (* 2 *fn2-nntp-line-cap*) *fn2-conn-range-min*)))

;; A query cursor's UPDATE (the link reads it): what its finished reply
;; moves the connection's selection to, or CLOSE: a reply that cannot be
;; completed after its status line went (a storage read failed mid-article),
;; so the connection closes rather than send a truncated block as complete.
(defconst *fn2-cursor-update-none* 0)
(defconst *fn2-cursor-update-current* 1)
(defconst *fn2-cursor-update-selection* 2)
(defconst *fn2-cursor-update-ihave* 3)
(defconst *fn2-cursor-update-close* 4)

(defmachine fn2-conn
 :states (:free :greeting :command :article-input :reply :upgrading :closing :draining :retired :query)
 :fields ((cap-index :u32) (cap-nonce :u32)
          (rx-slot :link) (rx-gen :u60) (tx-slot :link) (tx-gen :u60)
          (start :u32) (pos :u32) (overflow :bool) (compacting :bool) (cursor :u32)
          (tx-off :u32) (after (:enum fn2-conn-after (:command :article-input :upgrading :closing :query)))
          (pending :u32) (borrows :u32) (mask :u8) (ordinal :u32) (access-ref :u32)
          (auth-pending (:enum fn2-conn-auth (:none :user :sasl :redeem)))
          (tls-token :link) (tls-token-gen :u60) (tls-op :u32) (tls-op-gen :u60)
          (tls-stage (:enum fn2-conn-tls-stage (:none :admitted :running :finished))) (tls-ok :bool)
          (refused :bool) (stopped :bool) (next-free :link)
          ;; article input (D4, section 14.2): the upload this connection
          ;; feeds, the block's rule, the request it answers, the feed's
          ;; continuation, the outcome word posted back, the posting switch
          (upload :link) (upload-gen :u60) (rule (:enum fn2-conn-rule (:none :post :ihave :takethis)))
          (request :u32) (feed-mode :u8) (feed-discard :u8) (fed :u60) (word :u8) (outcome-ready :bool)
          (posting :bool)
          ;; the peer the Accept reported (A5r, a-pool-host-sim.md 4.1.1):
          ;; family (the listener's fn2-peer-family code), port, the address
          ;; in network order; read by the per-address and peer policy
          ;; (D5 3/n, D7 4/n), which lifts fn2-conn-reader-only-interim
          (peer-family :u8) (peer-port :u16) (peer-w0 :u32) (peer-w1 :u32) (peer-w2 :u32) (peer-w3 :u32)
          ;; reading (D6, section 15.3): the query cursor serving the line
          ;; [line-s, line-e), and the selection it reads (group, current
          ;; article, the view pinned at GROUP or LISTGROUP)
          (query :link) (query-gen :u60) (line-s :u32) (line-e :u32) (group :u60) (current :u60) (pin :u60))
 :links ((child-tls :kind fn2-tls-admit :slot tls-token :gen tls-token-gen :back (conn conn-gen) :reads (phase))
         (child-upload :kind fn2-upload :slot upload :gen upload-gen :back (conn conn-gen)
                       :reads (phase word))
         (child-cursor :kind fn2-cursor :slot query :gen query-gen :back (conn conn-gen)
                       :reads (turn done roff update sel ncurrent spin)))
 :holds ((:greeting :connection-row :rx-range :tx-range) (:command :connection-row :rx-range :tx-range)
         (:article-input :connection-row :rx-range :tx-range) (:reply :connection-row :rx-range :tx-range)
         (:upgrading :connection-row :rx-range :tx-range) (:closing :connection-row :rx-range :tx-range)
         (:draining :connection-row :rx-range :tx-range) (:query :connection-row :rx-range :tx-range))
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-profile-c profile)
 ;; The listener admits a connection into :greeting with its RX and TX
 ;; ranges reserved whole (A's generated fn2-machine-admit-fn2-conn).
 :admission (:phase :greeting :ranges (:rx-range :tx-range)
             :copy (principal-slot account-ref peer-family peer-port peer-w0 peer-w1 peer-w2 peer-w3)
             :clear (start pos overflow compacting cursor tx-off pending borrows ordinal refused
                     auth-pending tls-token-gen tls-op-gen tls-stage tls-ok access-ref upload-gen rule request feed-mode feed-discard fed word
                     outcome-ready posting query-gen line-s line-e group current pin))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (rx-slot *fn2-none*) (tx-slot *fn2-none*) (account-ref *fn2-none*) (next-free fn2-machine-initial-next-free)
           (upload *fn2-none*) (query *fn2-none*) (tls-token *fn2-none*) (tls-op *fn2-none*))
 :arms ((:free) (:greeting) (:command) (:article-input) (:reply) (:upgrading) (:closing) (:draining) (:retired) (:query))
 :observes ((:receive-result) (:send-result) (:borrow-released) (:close-result) (:tls-result) (:cancel-result)))

; MACHINE-FORM 6.5 P4: the kind's admission in child form, proved here;
; the admission section (assembly-callbacks-a) makes its core face.
(defmachine-registry fn2-conn)
