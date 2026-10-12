"""Shared environment boundary for isolated measurement processes."""


def sanitize_environment(env):
    return {key: value for key, value in env.items()
            if not key.startswith("FN_LOAD_") and key not in
            ("XL_HOOK", "XL_PROF", "XL_PROF_SECONDS", "XL_PROF_DIR")}
