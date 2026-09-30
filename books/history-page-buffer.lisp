; Concrete fixed-format page scratch for the disk-backed private writer.
; Page width comes from the existing persisted format, not a store ceiling.
(in-package "ACL2")

(defstobj fn-hpb
  (fn-hpb-w :type (array (unsigned-byte 64) (2048)) :initially 0)
  (fn-hpb-used :type (integer 0 2048) :initially 0)
  (fn-hpb-epoch :type t :initially nil)
  (fn-hpb-lease :type t :initially nil))

(defun fn-hpb-begin (epoch lease fn-hpb)
  ; Old array cells are not copied/zeroed. They are inaccessible through
  ; fn-hpb-word until overwritten into the new prefix.
  (declare (xargs :stobjs fn-hpb))
  (let* ((fn-hpb (update-fn-hpb-used 0 fn-hpb))
         (fn-hpb (update-fn-hpb-epoch epoch fn-hpb)))
    (update-fn-hpb-lease lease fn-hpb)))

(defun fn-hpb-put (w fn-hpb)
  (declare (xargs :stobjs fn-hpb :guard (unsigned-byte-p 64 w)))
  (let ((k (fn-hpb-used fn-hpb)))
    (if (<= 2048 k)
        (mv :full fn-hpb)
      (let* ((fn-hpb (update-fn-hpb-wi k w fn-hpb))
             (fn-hpb (update-fn-hpb-used (+ 1 k) fn-hpb)))
        (mv :stored fn-hpb)))))

(defun fn-hpb-word (i fn-hpb)
  (declare (xargs :stobjs fn-hpb :guard (and (natp i) (< i 2048))))
  ; A not-yet-written cell is never exposed as bytes from this page.
  (if (< i (fn-hpb-used fn-hpb))
      (mv :word (fn-hpb-wi i fn-hpb))
    (mv :unwritten 0)))

(defun fn-hpb-ready (fn-hpb)
  (declare (xargs :stobjs fn-hpb))
  (equal (fn-hpb-used fn-hpb) 2048))

; Logical abstraction. Host never calls it: serialization drains through
; the bounded word accessor, or a separately refined typed-array effect.
(defun fn-hpb-prefix-aux (i k fn-hpb)
  (declare (xargs :stobjs fn-hpb
                  :guard (and (natp i) (natp k) (<= (+ i k) 2048))))
  (if (zp k) nil
    (cons (fn-hpb-wi i fn-hpb)
          (fn-hpb-prefix-aux (+ 1 i) (1- k) fn-hpb))))

(defun fn-hpb-prefix (fn-hpb)
  (declare (xargs :stobjs fn-hpb))
  (fn-hpb-prefix-aux 0 (fn-hpb-used fn-hpb) fn-hpb))

(defthm fn-hpb-begin-empty
  (and (equal (fn-hpb-prefix (fn-hpb-begin epoch lease fn-hpb)) nil)
       (equal (fn-hpb-epoch (fn-hpb-begin epoch lease fn-hpb)) epoch)
       (equal (fn-hpb-lease (fn-hpb-begin epoch lease fn-hpb)) lease)))

(defthm fn-hpb-full-is-unchanged
  (implies (fn-hpb-ready fn-hpb)
           (and (equal (mv-nth 0 (fn-hpb-put w fn-hpb)) :full)
                (equal (mv-nth 1 (fn-hpb-put w fn-hpb)) fn-hpb))))

(defthm fn-hpb-put-keeps-identities
  (and (equal (fn-hpb-epoch (mv-nth 1 (fn-hpb-put w fn-hpb)))
              (fn-hpb-epoch fn-hpb))
       (equal (fn-hpb-lease (mv-nth 1 (fn-hpb-put w fn-hpb)))
              (fn-hpb-lease fn-hpb))))

(local
 (defthm fn-hpb-prefix-aux-used-frame
   (equal (fn-hpb-prefix-aux i k (update-fn-hpb-used v fn-hpb))
          (fn-hpb-prefix-aux i k fn-hpb))
   :hints (("Goal" :induct (fn-hpb-prefix-aux i k fn-hpb)))))

(local
 (defthm fn-hpb-word-after-update
   (implies (and (natp i) (natp j))
            (equal (fn-hpb-wi i (update-fn-hpb-wi j w fn-hpb))
                   (if (equal i j) w (fn-hpb-wi i fn-hpb))))))

(local
 (defthm fn-hpb-prefix-aux-put-end
   (implies (and (natp i) (natp k))
            (equal (fn-hpb-prefix-aux i (+ 1 k)
                                     (update-fn-hpb-wi (+ i k) w fn-hpb))
                   (append (fn-hpb-prefix-aux i k fn-hpb) (list w))))
   :hints (("Goal" :induct (fn-hpb-prefix-aux i k fn-hpb)
            :in-theory (disable update-fn-hpb-wi fn-hpb-wi)
            :expand ((fn-hpb-prefix-aux i 1 (update-fn-hpb-wi i w fn-hpb))
                     (fn-hpb-prefix-aux i (+ 1 k)
                                       (update-fn-hpb-wi (+ i k) w fn-hpb)))))))

(local
 (defthm fn-hpb-used-after-update
   (equal (fn-hpb-used (update-fn-hpb-used v fn-hpb)) v)))

(defthm fn-hpb-put-refines-prefix
  (implies (and (natp (fn-hpb-used fn-hpb))
                (< (fn-hpb-used fn-hpb) 2048))
           (and (equal (mv-nth 0 (fn-hpb-put w fn-hpb)) :stored)
                (equal (fn-hpb-prefix (mv-nth 1 (fn-hpb-put w fn-hpb)))
                       (append (fn-hpb-prefix fn-hpb) (list w)))))
  :hints (("Goal" :use ((:instance fn-hpb-prefix-aux-put-end (i 0) (k (fn-hpb-used fn-hpb))))
                  :in-theory (disable fn-hpb-prefix-aux
                                      update-fn-hpb-wi fn-hpb-wi update-fn-hpb-used fn-hpb-used))))

(defthm fn-hpb-begin-keeps-concrete
  (implies (fn-hpbp fn-hpb)
           (fn-hpbp (fn-hpb-begin epoch lease fn-hpb))))

(local
 (defthm fn-hpb-wp-update
   (implies (and (fn-hpb-wp words) (natp i) (< i (len words))
                 (unsigned-byte-p 64 w))
            (fn-hpb-wp (update-nth i w words)))
   :hints (("Goal" :induct (update-nth i w words)
            :in-theory (enable fn-hpb-wp)))))

(defthm fn-hpb-put-keeps-concrete
  (implies (and (fn-hpbp fn-hpb) (unsigned-byte-p 64 w))
           (fn-hpbp (mv-nth 1 (fn-hpb-put w fn-hpb)))))

(defthm fn-hpb-unwritten-never-exposes-old-word
  (implies (<= (fn-hpb-used fn-hpb) i)
           (equal (fn-hpb-word i fn-hpb) (mv :unwritten 0))))

(in-theory (disable fn-hpb-begin fn-hpb-put fn-hpb-word fn-hpb-prefix))
