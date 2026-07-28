"""Make ``src`` importable by the test suite without packaging boilerplate."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "src"))
