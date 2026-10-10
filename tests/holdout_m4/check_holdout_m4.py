"""M4 fresh holdouts: genuine Stdlib roots chosen after the freeze tag m4-freeze-1 (tests/holdout_lib.py)."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from lib import finish  # noqa: E402
from holdout_lib import run_holdouts  # noqa: E402

run_holdouts("m4-freeze-1", "holdout_m4", "m4/holdout_m4", Path(__file__).parent)
finish("test-holdout-m4")
