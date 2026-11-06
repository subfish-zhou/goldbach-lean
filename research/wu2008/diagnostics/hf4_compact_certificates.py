#!/usr/bin/env python3
"""Compatibility CLI: current constructive certificates; --panel keeps the legacy probe."""
import sys

if __name__ == '__main__':
    if any(arg == '--panel' or arg.startswith('--panel=') for arg in sys.argv[1:]):
        from hf4_constructive.lib.legacy_hf4 import main
    else:
        from hf4_constructive.produce import main
    main()
