; Actual initialization from the complete typed decoded lease.
(in-package "ACL2")
(include-book "decoded-window-descriptor")
(include-book "extent-window-compressed")

(defthm fn-pwz-dictionary-is-canonical-shipped-lookup
  (equal (fn-pwz-dictionary token)
         (and (fn-pwz-tokenp token) (fn-lzd-lookup (fn-pwz-nth 10 token))))
  :hints (("Goal" :in-theory (enable fn-pwz-dictionary fn-pwz-shipped-dictionary
                                    fn-pwz-nth fn-lzd-shipped
                                    fn-lzd-lookup fn-lzd-table fn-lzd-table-of)))
  :rule-classes nil)

(defthm fn-pwz-dictionary-is-bounded-octets
  (and (fn-cbor-octet-listp (fn-pwz-dictionary token))
       (<= (len (fn-pwz-dictionary token)) 65536))
  :hints (("Goal" :in-theory (enable fn-pwz-dictionary fn-pwz-shipped-dictionary
                                    fn-pwz-nth fn-lzd-shipped)))
  :rule-classes nil)

(defun fn-pwz-begin (token incarnation pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  :guard (fn-pwz-tokenp token)
                  :guard-hints (("Goal" :use fn-pwz-dictionary-is-bounded-octets))))
  ; The host does not choose a second dictionary or reconstruct coordinates.
  (fn-ewz-begin (nfix (fn-pwz-nth 2 token)) (nfix (fn-pwz-nth 3 token))
                (nfix (fn-pwz-nth 4 token)) (nfix (fn-pwz-nth 5 token))
                (nfix (fn-pwz-nth 6 token)) (nfix (fn-pwz-nth 9 token))
                (nfix (fn-pwz-nth 7 token)) (fn-pwz-nth 1 token) incarnation token
                (nfix (fn-pwz-nth 8 token)) (fn-pwz-dictionary token)
                pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))

(in-theory (disable fn-pwz-begin))
