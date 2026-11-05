;; Schema and partition registration for fn2-cursor (layer D, quest D6).
;; Arm bodies and helper operations live in books/cursor.lisp (a leaf book).
(in-package "ACL2")
(include-book "txn-kind")
(include-book "machines-c-read")
(include-book "machine-arms")
(include-book "machines-a-costs") ; fn2-machine-park: an :issue parks on :operation when the outbox is full
(fn2-book-layer :d)

(defmachine fn2-cursor
 :phases (:free :select :seek :render :send :fetch :finish :draining :retired)
 :fields ((conn :link) (conn-gen :u60) (conn-kind :u8) (mask :u8)
          (rx-slot :link) (rx-gen :u60) (line-s :u32) (line-e :u32) (tx-slot :link) (tx-gen :u60)
          (group :u60) (current :u60) (pin :u60)
          (tag :u8) (k0 :u8) (a0 :u32) (b0 :u32) (k1 :u8) (a1 :u32) (b1 :u32)
          (step :u8) (lo :u32) (hi :u32) (next :u32) (found :u32) (count :u32) (low :u32) (high :u32)
          (sel :u60) (ncurrent :u60) (spin :u60) (update :u8) (reply :u16) (roff :u32)
          (lpos :u32) (seen :bool) (have :u8) (turn :bool) (done :bool) (cancel :bool)
          (posting :bool) (lgroup :u60) (klen :u16)
          (stopped :bool) (next-free :link)
          ;; ARTICLE/HEAD/BODY (D6 3/n): the article, its location (unit,
          ;; allocation handle, length), the octets copied (APOS the piece's
          ;; first, PLEN its length, LOFF consumed of it, AST the stuffing
          ;; state), the lease, the 22x line's span in TX (OAT MSO MLN),
          ;; whether it went (SAID),
          ;; and the block read's result
          (art :u60) (lunit :u60) (lepoch :u60) (lalloc :u60) (alen :u60) (apos :u60) (plen :u32) (loff :u32)
          (ast :u8) (lslot :link) (lgen :u60) (lease (:enum fn2-cursor-lease (:none :held)))
          (oat :u32) (mso :u32) (mln :u32) (said :bool)
          (revent :u8) (routcome :u8) (rcount :u32) (rready :bool)
          ;; octets named through a source manifest (MKIND): the next entry's
          ;; manifest octet (MPOS), the block it names (BUNIT BEPOCH BALLOC
          ;; BLEN, BREADY once decoded) and whether the read in flight is the
          ;; manifest's (MREAD)
          (mkind :bool) (mpos :u32) (bunit :u60) (bepoch :u60) (balloc :u60) (blen :u32) (bready :bool) (mread :bool)
          ;; block reads in flight (the terminal of each completion consumes one)
          (pending :u32)
          ;; the pool class a row parked for its lease waits on (:park :pool's field)
          (cursor :u32))
 :holds ((:select :cursor-row (:storage-window :while (lease :held)))
         (:seek :cursor-row (:storage-window :while (lease :held)))
         (:render :cursor-row (:storage-window :while (lease :held)))
         (:send :cursor-row (:storage-window :while (lease :held)))
         (:fetch :cursor-row (:storage-window :while (lease :held)))
         (:finish :cursor-row (:storage-window :while (lease :held))) (:draining :cursor-row))
 :budget (:bytes 16384 :steps 32 :descriptors 4)
 :capacity (fn2-b-cursor-rows profile)
 :taken (:phase :select :rows :cursor-row :ranges ()
         :copy (conn conn-gen conn-kind mask rx-slot rx-gen line-s line-e tx-slot tx-gen group current pin posting)
         :clear (tag k0 a0 b0 k1 a1 b1 step lo hi next found count low high sel ncurrent spin update reply roff
                 lpos seen have turn done cancel stopped lgroup klen
                 art lunit lepoch lalloc alen apos plen loff ast lease oat mso mln said revent routcome rcount rready
                 mkind mpos bunit bepoch balloc blen bready mread cursor))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (conn *fn2-none*) (rx-slot *fn2-none*) (tx-slot *fn2-none*) (lslot *fn2-none*)
           (next-free fn2-machine-initial-next-free))
 :arms ((:free) (:select) (:seek) (:render) (:send) (:fetch) (:finish) (:draining) (:retired))
 :observes ((:read-result)))

(defmachine-registry fn2-cursor)
