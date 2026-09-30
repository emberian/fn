; One-byte salted FNV continuation for the current history MKEY column.
(in-package "ACL2")
(include-book "history-pages")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-hkc-begin (salt)
  (declare (xargs :guard (unsigned-byte-p 32 salt)))
  (mod (logxor *fn-hist-fnv-basis* salt) *fn-hist-u32-modulus*))

(defun fn-hkc-byte (octet hash)
  (declare (xargs :guard (and (unsigned-byte-p 8 octet) (unsigned-byte-p 32 hash))))
  (mod (* (logxor hash octet) *fn-hist-fnv-prime*) *fn-hist-u32-modulus*))

(defthm fn-hkc-begin-is-u32
  (implies (unsigned-byte-p 32 salt) (unsigned-byte-p 32 (fn-hkc-begin salt)))
  :hints (("Goal" :in-theory (disable mod logxor))))
(defthm fn-hkc-byte-is-u32
  (implies (and (unsigned-byte-p 8 octet) (unsigned-byte-p 32 hash))
           (unsigned-byte-p 32 (fn-hkc-byte octet hash)))
  :hints (("Goal" :in-theory (disable mod logxor))))

; Resident string client. Cold string spans use the same byte core after
; their pinned reader supplies one source byte, under its position token.
(defun fn-hkc-tick (source index hash)
  (declare (xargs :guard (and (stringp source) (natp index)
                              (unsigned-byte-p 32 hash))))
  (if (< index (length source))
      (mv :continue (+ 1 index) (fn-hkc-byte (char-code (char source index)) hash))
    (mv :done index hash)))

(defun fn-hkc-result (hash)
  (declare (xargs :guard (unsigned-byte-p 32 hash)))
  (+ 1 hash))

(defthm fn-hkc-begin-refines-current-hash
  (implies (unsigned-byte-p 32 salt)
           (equal (fn-hist-fnv source 0 (fn-hkc-begin salt))
                  (fn-hist-hash source salt)))
  :hints (("Goal" :in-theory (e/d (fn-hist-hash) (fn-hist-fnv)))))

(defthm fn-hkc-byte-preserves-current-residual
  (implies (and (stringp source) (natp index) (< index (length source))
                (unsigned-byte-p 32 hash)
                (equal octet (char-code (char source index))))
           (equal (fn-hist-fnv source (+ 1 index) (fn-hkc-byte octet hash))
                  (fn-hist-fnv source index hash)))
  :hints (("Goal" :expand ((fn-hist-fnv source index hash))
           :in-theory (disable fn-hist-fnv mod logxor))))

(defthm fn-hkc-tick-preserves-current-residual
  (implies (and (stringp source) (natp index) (unsigned-byte-p 32 hash))
           (equal (fn-hist-fnv source (mv-nth 1 (fn-hkc-tick source index hash))
                              (mv-nth 2 (fn-hkc-tick source index hash)))
                  (fn-hist-fnv source index hash)))
  :hints (("Goal" :in-theory (disable fn-hist-fnv fn-hkc-byte))))

(defthm fn-hkc-terminal-refines-current-key
  (implies (and (stringp source) (natp index) (unsigned-byte-p 32 hash)
                (equal (mv-nth 0 (fn-hkc-tick source index hash)) :done))
           (equal (fn-hkc-result (mv-nth 2 (fn-hkc-tick source index hash)))
                  (+ 1 (fn-hist-fnv source index hash))))
  :hints (("Goal" :expand ((fn-hist-fnv source index hash))
           :in-theory (disable fn-hist-fnv fn-hkc-byte))))

(defthm fn-hkc-tick-keeps-domain
  (implies (and (stringp source) (natp index) (unsigned-byte-p 32 hash))
           (and (natp (mv-nth 1 (fn-hkc-tick source index hash)))
                (unsigned-byte-p 32 (mv-nth 2 (fn-hkc-tick source index hash)))))
  :hints (("Goal" :use ((:instance fn-hkc-byte-is-u32
                                   (octet (char-code (char source index)))))
           :in-theory (disable fn-hkc-byte fn-hkc-byte-is-u32))))

(in-theory (disable fn-hkc-begin fn-hkc-byte fn-hkc-tick fn-hkc-result))


; This boundary consumes the maintained residual equality. It does not scan
; the event or Message-ID as an executable preflight.
(defthm fn-hkc-complete-refines-current-mkey
  (implies (and (equal source (fn-hist-key-msgid ev)) (stringp source)
                (natp index) (unsigned-byte-p 32 hash)
                (equal (fn-hist-fnv source index hash) (fn-hist-hash source salt))
                (equal (mv-nth 0 (fn-hkc-tick source index hash)) :done))
           (equal (fn-hkc-result (mv-nth 2 (fn-hkc-tick source index hash)))
                  (fn-hp-mkey ev salt)))
  :hints (("Goal" :in-theory (e/d (fn-hp-mkey)
                                  (fn-hkc-tick fn-hkc-result fn-hist-fnv fn-hist-hash
                                   fn-hist-key-msgid)))))

(defthm fn-hkc-tick-progress
  (implies (and (stringp source) (natp index)
                (equal (mv-nth 0 (fn-hkc-tick source index hash)) :continue))
           (and (equal (mv-nth 1 (fn-hkc-tick source index hash)) (+ 1 index))
                (< (nfix (- (length source) (mv-nth 1 (fn-hkc-tick source index hash))))
                   (nfix (- (length source) index)))))
  :hints (("Goal" :in-theory (e/d (fn-hkc-tick) (fn-hkc-byte length)))))
