# Released fn worktree retirement, 2026-09-24

Against `dev` `c12f4f28`, five owner-released, clean and process-free worktrees
were archived under the private local
`/Users/ember/dev/fn-worktree-archive/20260924/` and removed normally with
`git worktree remove`. Their original branch refs and tips remain. This is
workspace retirement, not new proof or native qualification.

| Retired lane | Retained tip | Archive SHA-256 prefix | Landing check |
| --- | --- | --- | --- |
| `k0-frontier-eio-choices` | `45c68797` | `cb67c632544c` | Its frontier EIO choice theorem family remains in dev after later book edits. |
| `owner-retention-preparation` | `86bc8d41` | `ddcf3e7d67f2` | Book and ACL2 test bytes match dev. |
| `consumer-config-open-index` | `a8bce5c4` | `dd45e0896318` | All branch commits are patch-equivalent to dev. |
| `consumer-poll-teeth` | `f6822e6c` | `5cee64ac6c6a` | All branch commits are patch-equivalent to dev. |
| `topic-preservation-native` | `6453a08b` | `d106efc04a61` | Branch commit is patch-equivalent to dev. |

For each lane, `git status --porcelain` was empty; an `lsof` working-directory
scan found no process in its path; the complete tar/zstd archive was extracted
to temporary staging and every regular-file byte and symlink target was
compared with the original, including ignored files and the `.git` pointer.
The source was compared again before removal. The archive SHA-256 and retained
branch tip were checked after removal. The corresponding private `<lane>.json`
manifest records full hashes, entry count, original path and restore
instructions. This batch archived 479,879,691 logical regular-file bytes into
71,122,013 archive bytes. The local archive README now records 117 retired
worktrees in total. No branch was deleted; no remote gate, proof cache,
service, Mini tree, active BP/ION/peer lane or native-qualification tree was
touched.

The live work queue remains the owner handoffs in
[the disposition audit](worktree-disposition-2026-09-24.md). In particular,
the unadmitted BP draft was subsequently removed by its owner, and its open
proof obligation remains in their handoff; the peer-authored lane reached a
new clean finite tip after that audit's snapshot. Inspect current tips before
integrating any packet.
