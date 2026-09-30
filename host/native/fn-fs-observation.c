/* Raw filesystem observation, not admission or byte-count policy.
 * PATH and WORDS are caller-owned native storage retained until this call
 * returns. No Lisp heap pointer crosses the blocking syscall. The caller
 * must separately admit result interpretation and retain both buffers on
 * an uncertain/nonlocal exit. libc/kernel allocation remains a qualification
 * obligation; this wrapper itself uses only fixed automatic storage.
 */
#include <limits.h>
#include <stdint.h>
#include <sys/statvfs.h>

#define FN_EXPORT __attribute__((visibility("default")))
_Static_assert(CHAR_BIT == 8, "native observation requires octet-addressed storage");
_Static_assert(sizeof(((struct statvfs *)0)->f_frsize) <= sizeof(uint64_t),
               "fragment size must fit the observed u64 field");
_Static_assert(sizeof(((struct statvfs *)0)->f_bavail) <= sizeof(uint64_t),
               "available blocks must fit the observed u64 field");

FN_EXPORT int fn_fs_space_observe(const char *path, uint32_t words[4])
{
    struct statvfs observation;
    int result = statvfs(path, &observation);
    if (result == 0) {
        uint64_t fragment_size = (uint64_t)observation.f_frsize;
        uint64_t available_blocks = (uint64_t)observation.f_bavail;
        /* Explicit low/high words avoid Lisp bignum allocation on return.
         * These are scalar stores, independent of host byte order. */
        words[0] = (uint32_t)fragment_size;
        words[1] = (uint32_t)(fragment_size >> 32);
        words[2] = (uint32_t)available_blocks;
        words[3] = (uint32_t)(available_blocks >> 32);
    }
    /* On failure the old words are retained; RESULT alone reports this
     * syscall. A previous successful payload is never new evidence. */
    return result;
}
