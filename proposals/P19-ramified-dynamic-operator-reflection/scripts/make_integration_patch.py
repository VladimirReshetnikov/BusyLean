#!/usr/bin/env python3
"""Regenerate patches/integration.patch from the overlay sources."""
from __future__ import annotations

import difflib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "patches" / "integration.patch"


def new_file_patch(path: str) -> str:
    lines = (ROOT / path).read_text(encoding="utf-8").splitlines(True)
    header = f"diff --git a/{path} b/{path}\nnew file mode 100644\n"
    body = difflib.unified_diff(
        [], lines, fromfile="/dev/null", tofile=f"b/{path}", n=3
    )
    return header + "".join(body)


prefix = r'''diff --git a/BusyLean.lean b/BusyLean.lean
--- a/BusyLean.lean
+++ b/BusyLean.lean
@@ -20,4 +20,6 @@
 import BusyLean.Contender12
 import BusyLean.Comparison12
 import BusyLean.Contender13
 import BusyLean.Comparison13
+import BusyLean.Contender14
+import BusyLean.Comparison14
diff --git a/scripts/check.py b/scripts/check.py
--- a/scripts/check.py
+++ b/scripts/check.py
@@ -28,7 +28,7 @@
 BUILD_DIRS = [ROOT / ".lake" / "build",
               ROOT / "proposals" / "P5-w-reflection" / "lean" / ".lake" / "build"]
 PERMITTED = {"propext", "Quot.sound"}
-PREVIOUS = "BusyLean.Comparison12"   # previous contender: definitions + proofs
-CURRENT_DEF = "BusyLean.Contender13"  # current contender's definition module
+PREVIOUS = "BusyLean.Comparison13"   # previous contender: definitions + proofs
+CURRENT_DEF = "BusyLean.Contender14"  # current contender's definition module
 DEFINITION_BUDGET = 15.0  # seconds
 PROOF_BUDGET = 60.0
diff --git a/test/Audit.lean b/test/Audit.lean
--- a/test/Audit.lean
+++ b/test/Audit.lean
@@ -150,5 +150,20 @@
 #check @BusyLean.Fd.sn_of_typed
 #check @BusyLean.Fk.sn_of_typed
 
 -- The final family is a genuine computable function (only input 0 is feasible).
 #eval BusyLean.finalFamily 0
+
+-- Contender 14 additions.
+#print axioms BusyLean.contender_14
+#print axioms BusyLean.contender_13_lt_contender_14
+#print axioms BusyLean.fortyTwo_F13_steps_lt_F14
+#print axioms BusyLean.fvalue_lt_contender_14
+
+#assert_not_in_closure BusyLean.contender_14 :
+  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
+  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
+  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5
+
+#check @BusyLean.contender_13_lt_contender_14
+#check @BusyLean.fortyTwo_F13_steps_lt_F14
+#check @BusyLean.fvalue_lt_contender_14
'''

paths = [
    "BusyLean/Contender14.lean",
    "BusyLean/Comparison14.lean",
    "test/Contender14Audit.lean",
    "article/contender14_rdor.tex",
]
OUT.write_text(prefix + "".join(new_file_patch(p) for p in paths), encoding="utf-8")
print(OUT)
