;; Schema and partition registration for fn2-cursor (layer D, quest D6).
;; Arm bodies and helper operations live in books/cursor.lisp (a leaf book).
(in-package "ACL2")
(include-book "txn-kind")
(include-book "machines-c-read")
(include-book "machine-arms")
(fn2-book-layer :d)

(defmachine fn2-cursor
 :phases (:free :select :seek :render :send :finish :draining :retired)
 :fields ((conn :link) (conn-gen :u60) (conn-kind :u8) (mask :u8)
          (rx-slot :link) (rx-gen :u60) (line-s :u32) (line-e :u32) (tx-slot :link) (tx-gen :u60)
          (group :u60) (current :u60) (pin :u60)
          (tag :u8) (k0 :u8) (a0 :u32) (b0 :u32) (k1 :u8) (a1 :u32) (b1 :u32)
          (step :u8) (lo :u32) (hi :u32) (next :u32) (found :u32) (count :u32) (low :u32) (high :u32)
          (sel :u60) (ncurrent :u60) (spin :u60) (update :u8) (reply :u16) (roff :u32)
          (lpos :u32) (seen :bool) (have :u8) (turn :bool) (done :bool) (cancel :bool)
          (posting :bool) (lgroup :u60) (klen :u16)
          (stopped :bool) (next-free :link))
 :holds ((:select :cursor-row) (:seek :cursor-row) (:render :cursor-row) (:send :cursor-row)
         (:finish :cursor-row) (:draining :cursor-row))
 :budget (:bytes 16384 :steps 32 :descriptors 4)
 :capacity (fn2-b-cursor-rows profile)
 :taken (:phase :select :rows :cursor-row :ranges ()
         :copy (conn conn-gen conn-kind mask rx-slot rx-gen line-s line-e tx-slot tx-gen group current pin posting)
         :clear (tag k0 a0 b0 k1 a1 b1 step lo hi next found count low high sel ncurrent spin update reply roff
                 lpos seen have turn done cancel stopped lgroup klen))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (conn *fn2-none*) (rx-slot *fn2-none*) (tx-slot *fn2-none*) (next-free fn2-machine-initial-next-free))
 :arms ((:free) (:select) (:seek) (:render) (:send) (:finish) (:draining) (:retired))
 :observes ())

(defmachine-registry fn2-cursor)
