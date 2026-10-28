; Actual A declaration, isolated so continuation edits reuse its certificate.
; Include core FIRST: the sprint sidecar does not change the closed A core.
(in-package "ACL2")
(include-book "../../books/core")

(defconst *fn2-sd-supported-profile*
  '((:max-article-octets . 1024) (:storage-bytes . 131072)))

(defmachine fn2-sdconn
 :states (:accepting :greeting :command :article-input :reply :group-select :lookup :render :post-check :log-write :fence :publish :closing :draining :done)
 :fields ((rx-slot :u32) (rx-gen :u60) (tx-slot :u32) (tx-gen :u60)
          (up-slot :u32) (up-gen :u60) (cap-index :u32) (cap-nonce :u32)
          (scan :u32) (start :u32) (selected :u60) (after-reply :u8)
          (tx-off :u32) (tx-len :u32) (pending :u32) (op-slot :u32) (op-gen :u60)
          (request :u8) (arg-off :u32) (arg-len :u32) (query :u60) (seek :u32)
          (summary-count :u60) (summary-low :u60) (summary-high :u60)
          (mid-off :u32) (mid-len :u32) (post-len :u32) (storage-bytes :u60) (article-limit :u32) (outcome :u8) (ordinal :u60))
 :accounts (:operations :bytes :row)
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity 1
 :initial ((storage-bytes 131072) (generation gen) (ready-prev 4294967295) (ready-next 4294967295))
 :continuations
 ((:accepting (fn2-sd-issue id budget fn2-sdconn fn2-core fn2-sprint-c))
  (:greeting (fn2-sd-greet id budget fn2-sdconn fn2-core fn2-sprint-c))
  (:command (fn2-sd-input id budget nil fn2-sdconn fn2-core fn2-sprint-c))
  (:article-input (fn2-sd-input id budget t fn2-sdconn fn2-core fn2-sprint-c))
  (:reply (fn2-sd-send id budget fn2-sdconn fn2-core fn2-sprint-c))
  (:group-select (fn2-sd-group id budget fn2-sdconn fn2-core fn2-sprint-c))
  (:lookup (fn2-sd-lookup id budget fn2-sdconn fn2-core fn2-sprint-c))
  (:render (fn2-sd-render id budget fn2-sdconn fn2-core fn2-sprint-c))
  (:post-check (fn2-sd-post-check id budget fn2-sdconn fn2-core fn2-sprint-c))
  (:log-write (fn2-sd-issue id budget fn2-sdconn fn2-core fn2-sprint-c))
  (:fence (fn2-sd-issue id budget fn2-sdconn fn2-core fn2-sprint-c))
  (:publish (fn2-sd-publish id budget fn2-sdconn fn2-core fn2-sprint-c))
  (:closing (fn2-sd-issue id budget fn2-sdconn fn2-core fn2-sprint-c))
  (:draining (fn2-sd-drain id budget fn2-sdconn fn2-core fn2-sprint-c))
  (:done (fn2-sd-idle id budget fn2-sdconn fn2-core fn2-sprint-c))))

