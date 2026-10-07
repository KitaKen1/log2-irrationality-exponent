"""Backward-compatible entry point for the default three-module rc4 check."""
from check_rc4_compat import main

if __name__ == '__main__':
    raise SystemExit(main())
