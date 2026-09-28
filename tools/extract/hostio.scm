;;; tools/extract/hostio.scm -- the host primitives of an extracted program
;;; (lane extract-2): host/store-open-host.lisp's `fn-hx-' stubs and the
;;; durable-extent realizers (A-DURABLE-EXTENT), in the trust boundary beside
;;; runtime.scm.  Filesystem syscalls that decide nothing: every answer goes
;;; back to ACL2 as a value, and every refusal text is ACL2's or io.lisp's.
;;; A HANDLE is an index into one table of read-only descriptors held for the
;;; process's life (never closed, never reused: an unlinked segment stays
;;; readable); it is also the realizer's durable FILE id.
(foreign-declare "
#include <fcntl.h>
#include <unistd.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include <sys/stat.h>
#include <sys/file.h>
#ifdef __linux__
#include <sys/vfs.h>
#else
#include <sys/param.h>
#include <sys/mount.h>
#endif
static long fnx_lstat(const char *p, int want_size) {
  struct stat st;
  if (lstat(p, &st) != 0) return errno == ENOENT ? -1 : -2;
  if (want_size) return (long) st.st_size;
  if (S_ISREG(st.st_mode)) return 1;
  if (S_ISDIR(st.st_mode)) return 2;
  if (S_ISLNK(st.st_mode)) return 3;
  return 4;
}
static long fnx_open(const char *p) {
  int fd = open(p, O_RDONLY | O_NOFOLLOW);
  return fd < 0 ? -(long) errno : fd;
}
static long fnx_fsize(int fd) {
  struct stat st;
  if (fstat(fd, &st) != 0) return -1;
  return S_ISREG(st.st_mode) ? (long) st.st_size : -2;
}
static long fnx_pread(int fd, unsigned char *buf, size_t n, long off) {
  size_t done = 0;
  while (done < n) {
    ssize_t r = pread(fd, buf + done, n - done, off + (long) done);
    if (r > 0) done += (size_t) r;
    else if (r == 0) break;
    else if (errno == EINTR) continue;
    else return -1;
  }
  return (long) done;
}
static long fnx_pwrite(int fd, unsigned char *buf, size_t n, long off) {
  size_t done = 0;
  while (done < n) {
    ssize_t r = pwrite(fd, buf + done, n - done, off + (long) done);
    if (r > 0) done += (size_t) r;
    else if (r < 0 && errno == EINTR) continue;
    else return -1;
  }
  return (long) done;
}
static long fnx_lock_shared(const char *p) {
  int fd = open(p, O_RDONLY | O_NOFOLLOW);
  struct stat st;
  if (fd < 0) return -(long) errno;
  if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode)) { close(fd); return 1000000; }
  if (flock(fd, LOCK_SH | LOCK_NB) != 0) { close(fd); return 1000001; }
  return fd;
}
static long fnx_fsync_dir(const char *p) {
  int fd = open(p, O_RDONLY | O_DIRECTORY);
  if (fd < 0) return -(long) errno;
  if (fsync(fd) != 0) { int e = errno; close(fd); return -(long) e; }
  close(fd);
  return 0;
}
static int fnx_statfs(const char *p, unsigned char *buf) {
  memset(buf, 0, 4096);
  return statfs(p, (void *) buf) == 0 ? 0 : -1;
}
")

(define %lstat (foreign-lambda long "fnx_lstat" c-string int))
(define %open (foreign-lambda long "fnx_open" c-string))
(define %fsize (foreign-lambda long "fnx_fsize" int))
(define %pread (foreign-lambda* long ((int fd) (u8vector buf) (size_t n) (long off))
                 "C_return(fnx_pread(fd, buf, n, off));"))
(define %pwrite (foreign-lambda* long ((int fd) (u8vector buf) (size_t start) (size_t n) (long off))
                  "C_return(fnx_pwrite(fd, buf + start, n, off));"))
(define %lock-shared (foreign-lambda long "fnx_lock_shared" c-string))
(define %fsync-dir (foreign-lambda long "fnx_fsync_dir" c-string))
(define %statfs (foreign-lambda int "fnx_statfs" c-string u8vector))
(define %realpath (foreign-lambda* c-string* ((c-string p)) "C_return(realpath(p, NULL));"))
(define %opendir (foreign-lambda c-pointer "opendir" c-string))
(define %readdir-name
  (foreign-lambda* c-string ((c-pointer d))
    "struct dirent *e = readdir((DIR *) d); C_return(e ? e->d_name : NULL);"))
(define %closedir (foreign-lambda int "closedir" c-pointer))

(define kw-ok '|KEYWORD::OK|)
(define kw-error '|KEYWORD::ERROR|)

;; the handle table: handle -> (fd . path)
(define hx-handles (make-vector 16 #f))
(define hx-next 1)
(define (hx-register fd path)
  (when (fx>= hx-next (vector-length hx-handles))
    (set! hx-handles (vector-resize hx-handles (fx* 2 (vector-length hx-handles)) #f)))
  (vector-set! hx-handles hx-next (cons fd path))
  (set! hx-next (fx+ hx-next 1))
  (fx- hx-next 1))
(define (hx-fd h)
  (let ((e (and (fixnum? h) (fx> h 0) (fx< h hx-next) (vector-ref hx-handles h))))
    (if e (car e) (error (sprintf "arena-extent-read: no durable file ~a is registered" h)))))
(define (hx-path h) (let ((e (vector-ref hx-handles h))) (if e (cdr e) "?")))

(define (a-hx-lstat path)
  (let ((k (%lstat path 0)))
    (case k
      ((-1) (list '|KEYWORD::ABSENT|))
      ((1) (list '|KEYWORD::REGULAR| (%lstat path 1)))
      ((2) (list '|KEYWORD::DIRECTORY|))
      ((3) (list '|KEYWORD::SYMLINK|))
      (else (list '|KEYWORD::OTHER|)))))

(define (a-hx-list-dir path limit)
  (let ((d (%opendir path)))
    (if (not d)
        (list kw-error "opendir")
        (let loop ((names '()) (count 0))
          (let ((name (%readdir-name d)))
            (cond ((not name) (%closedir d) (list kw-ok (reverse names) '()))
                  ((or (string=? name ".") (string=? name "..")) (loop names count))
                  ((>= count limit) (%closedir d) (list kw-ok (reverse names) '|COMMON-LISP::T|))
                  (else (loop (cons name names) (fx+ count 1)))))))))

(define (a-hx-open path)
  (let ((fd (%open path)))
    (if (< fd 0)
        (list kw-error (- fd) "open")
        (let ((size (%fsize fd)))
          (cond ((= size -1) (list kw-error 0 "fstat"))
                ((= size -2) (list kw-ok (hx-register fd path) 0 '()))
                (else (list kw-ok (hx-register fd path) size '|COMMON-LISP::T|)))))))

(define (hx-pread-u8 h off n)
  (let* ((buf (make-u8vector n 0))
         (got (%pread (hx-fd h) buf n off)))
    (cond ((< got 0) #f)
          ((= got n) buf)
          (else (subu8vector buf 0 got)))))

(define (a-hx-pread h off n)
  (let ((buf (hx-pread-u8 h off n)))
    (if buf (list kw-ok (u8vector->list buf)) (list kw-error "pread"))))

;; the log walk's buffer (fn-octets-lg, foundation fn-octets$c: slot 0 the
;; array, slot 1 the fill) holds exactly the entry, as io.lisp sets it
(define (a-hx-fill h off n buf)
  (let ((v (if (eqv? n 0) (make-u8vector 0 0) (hx-pread-u8 h off n))))
    (if v
        (begin (vector-set! buf 0 v) (vector-set! buf 1 (u8vector-length v))
               (values (u8vector-length v) buf))
        (values -1 buf))))

(define (a-hx-lock-shared path)
  (let ((r (%lock-shared path)))
    (cond ((= r 1000000) '|KEYWORD::NOT-REGULAR|)
          ((= r 1000001) '|KEYWORD::LOCKED|)
          ((< r 0) (list kw-error (- r) "open"))
          (else kw-ok))))

(define (a-hx-fsync-dir path)
  (if (= (%fsync-dir path) 0) kw-ok (list kw-error "fsync")))

(define (a-hx-statfs path)
  (let ((buf (make-u8vector 4096 0)))
    (if (= (%statfs path buf) 0) (u8vector->list buf) '())))

(define (a-hx-realpath path)
  (let ((r (%realpath path)))
    (if r (map char->integer (string->list r)) '())))

(define (a-hx-os)
  (cond-expand (linux '|KEYWORD::LINUX|) (openbsd '|KEYWORD::OPENBSD|)
               (macosx '|KEYWORD::DARWIN|) (else '|KEYWORD::OTHER|)))

(define (a-hx-warn text)
  (let ((port (current-error-port))) (display text port) (newline port) '()))

;; The page store's two byte primitives (host/native/proto-pagestore-io.lisp
;; fnps-fill-from-file / fnps-write-to-file): a u8vector range from or to a
;; file at a byte offset; a short read is end of file, refused by name.
(define %pread-at (foreign-lambda* long ((int fd) (u8vector buf) (size_t start) (size_t n) (long off))
                    "C_return(fnx_pread(fd, buf + start, n, off));"))
(define (a-hx-fill-from-file h byte-offset vec start count)
  (let ((got (%pread-at (hx-fd h) vec start count byte-offset)))
    (unless (= got count)
      (error (sprintf "pread: end of file at byte ~a" (+ byte-offset (max got 0)))))
    count))
(define (a-hx-write-to-file h byte-offset vec start count)
  (unless (= (%pwrite (hx-fd h) vec start count byte-offset) count)
    (error "pwrite failed"))
  count)

(define (remove-eq x l) (cond ((null? l) '()) ((eq? x (car l)) (cdr l)) (else (cons (car l) (remove-eq x (cdr l))))))

;; --- the durable-extent realizers (host/native/extent.lisp) -------------------
;; An entry's protected prefix and trailer read once (one pread), checked by
;; ACL2 (fn-arx-entry-ok-buffer over the realizer's buffer fn-octets-rd, its
;; array the octets read and its fill the prefix's length), kept in a cache
;; of ACL2's size (fn-arx-read-cache-entries), most recent first.  The two
;; ACL2 calls are the raw procedures: the image makes them through fnn-call
;; inside the outer entry's call, and both guards are T.
(define extent-cache '())
(define extent-rd #f)
(define (extent-entry file eoff elen)
  (let ((hit (let find ((c extent-cache))
               (cond ((null? c) #f)
                     ((and (eqv? (car (car c)) file) (eqv? (cadr (car c)) eoff)) (car c))
                     (else (find (cdr c)))))))
    (if hit
        (begin (unless (eq? hit (car extent-cache))
                 (set! extent-cache (cons hit (remove-eq hit extent-cache))))
               (cddr hit))
        (let* ((fd (hx-fd file))
               (octets (make-u8vector (+ elen 32) 0))
               (got (%pread fd octets (+ elen 32) eoff)))
          (unless (= got (+ elen 32))
            (error (sprintf "arena-extent-read: ~a at ~a holds fewer than ~a octets"
                            (hx-path file) eoff (+ elen 32))))
          (unless extent-rd (set! extent-rd (|f:ACL2::CREATE-FN-OCTETS$C|)))
          (vector-set! extent-rd 0 octets)
          (vector-set! extent-rd 1 elen)
          (let ((ok (call-with-values
                        (lambda () (|f:ACL2::FN-ARX-ENTRY-OK-BUFFER|
                                    (u8vector->list (subu8vector octets elen (+ elen 32))) extent-rd))
                      (lambda vs (car vs)))))
            (vector-set! extent-rd 1 0)
            (vector-set! extent-rd 0 (make-u8vector 0 0))
            (unless (eq? ok '|COMMON-LISP::T|)
              (error (sprintf "arena-extent-digest: the entry at ~a of ~a does not match its trailer"
                              eoff (hx-path file)))))
          (let ((limit (|f:ACL2::FN-ARX-READ-CACHE-ENTRIES|)))
            (when (> limit 0)
              (set! extent-cache (cons (cons file (cons eoff octets)) extent-cache))
              (when (> (length extent-cache) limit)
                (set! extent-cache (list-head extent-cache limit)))))
          octets))))
(define (a-durable-realize-octet file eoff elen poff plen trailer i)
  (u8vector-ref (extent-entry file eoff elen) (+ (- poff eoff) i)))
(define (a-durable-realize-octets file eoff elen poff plen trailer)
  (let ((entry (extent-entry file eoff elen)) (start (- poff eoff)))
    (let loop ((i (+ start plen -1)) (acc '()))
      (if (< i start) acc (loop (- i 1) (cons (u8vector-ref entry i) acc))))))

;; A-DURABLE-LZ's realizer (host/native/extent.lisp fn-durable-realize-lz):
;; the block read through the extent realizer (trailer checked), ACL2's
;; decoder fn-lzr-lz-read over it (called as the host calls it, through the
;; boundary), its octets answered; a failed decode refused by name.  The last
;; decoded payload is kept (key: file, entry, block, length; the dictionary by
;; identity), so an octet-by-octet reader decodes once.
(define extent-lz-last #f)
(define (a-durable-realize-lz file eoff elen poff plen trailer n dict)
  (let ((key (list file eoff poff plen n)))
    (if (and extent-lz-last (equal? (car extent-lz-last) key) (eq? (cadr extent-lz-last) dict))
        (cddr extent-lz-last)
        (let* ((c (a-durable-realize-octets file eoff elen poff plen trailer))
               (saved a-current-entry)
               (r (|b:ACL2::FN-LZR-LZ-READ| dict c n)))
          (set! a-current-entry saved)
          (unless (and (pair? r) (eq? (car r) '|KEYWORD::OK|))
            (error (sprintf "arena-extent-lz-decode: the block at ~a of ~a does not decode to its ~a octets"
                            poff (hx-path file) n)))
          (set! extent-lz-last (cons key (cons dict (cadr r))))
          (cadr r)))))
