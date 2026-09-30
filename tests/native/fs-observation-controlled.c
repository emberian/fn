/* Tests execute the production C body with only statvfs replaced. */
#include <pthread.h>
#include <stdint.h>
#include <string.h>
#include <sys/statvfs.h>
static pthread_mutex_t gate = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t ready = PTHREAD_COND_INITIALIZER;
static int entered, released;
int fn_fs_test_entered(void)
{
    int result;
    pthread_mutex_lock(&gate);
    result = entered;
    pthread_mutex_unlock(&gate);
    return result;
}
void fn_fs_test_release(void)
{
    pthread_mutex_lock(&gate);
    released = 1;
    pthread_cond_broadcast(&ready);
    pthread_mutex_unlock(&gate);
}
static int controlled_statvfs(const char *path, struct statvfs *out)
{
    if (path[0] == 'f') return -1;
    if (path[0] == 'b') {
        pthread_mutex_lock(&gate);
        entered = 1;
        pthread_cond_broadcast(&ready);
        while (!released) pthread_cond_wait(&ready, &gate);
        pthread_mutex_unlock(&gate);
    }
    memset(out, 0, sizeof *out);
    out->f_frsize = UINT64_C(0xfedcba9876543210);
    out->f_bavail = UINT64_C(0x89abcdef01234567);
    return 0;
}
#define statvfs(path, out) controlled_statvfs(path, out)
#define fn_fs_space_observe fn_fs_space_observe_test
#include "../../host/native/fn-fs-observation.c"
