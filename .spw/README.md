# Spw Workspace

This `.spw` tree is consumer-owned. `_workbench` is mounted infrastructure: use its machinery, but exclude it from the consumer corpus unless infrastructure is the explicit subject.

## Orient

```bash
npm --prefix .spw/_workbench run spw -- doctor ../..
npm --prefix .spw/_workbench run spw -- roots
npm --prefix .spw/_workbench run spw -- tree @spw --depth 3
npm --prefix .spw/_workbench run spw -- select .spw/index.spw --selector navigable --summary
```

## Model Prompt

Read this file, `index.spw`, `workspace.spw`, and `mount.spw`. Treat `_workbench` as mounted infrastructure and optionally use `_workbench/.agents/skills/spw-mounted-consumer-review/SKILL.md` as an instrument. Existing fn authority and the requested four-axis audit prevail; mounted skills add no approval gates. Review one bounded question against consumer-owned files, record both repository revisions, and write portable evidence under `.spw/audits/`.

Working references:

- `_workbench/docs/runtime/md/mounted-workbench.md`
- `_workbench/.spw/conventions/submodule.spw`
- `_workbench/.agents/skills/spw-mounted-consumer-review/SKILL.md`

## fn review map

Start at `machines.spw`; follow each source and specification reference before trusting the map. The entry audit owns this shared map; independent findings live in `audits/entries`, `audits/exits`, `audits/consistency`, and `audits/bounds`. A machine card distinguishes catalogued, executable definitions read, scenarios mentally traced, tested, and proved. Coverage gaps stay explicit.

Every finding records source revision, function, triggering transition, boundary contract, observed evidence, disposition, and residual work. Cross-link another horse's finding by relative path instead of copying its status. Spw references navigate files; named symbols are text coordinates until a source symbol index exists.

The initializer also installs a commit-review workflow and pre-commit hook; this side effect requires care in an already active repository. Dependency installation was needed before CLI invocation. Commands and friction are recorded in `audits/entries/tooling.md`.

Mounted checkout source: https://github.com/spwashi/spw-workbench.git at651b535b5171. Consumer `.gitignore` excludes the independent checkout; pin and source live in mount.spw. Clone/install deliberately when reconstructing this workspace. Avoid `spw init` on an active repository unless its hook/workflow side effects are wanted; the four consumer files can be maintained directly.
