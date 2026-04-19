"""
AI Formalizer Test Suite
Runs 10 example conversions and validates basic syntax correctness.
"""

import sys
import os
import re
from typing import List

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from core import formalize, formalize_simple


# ---------------------------------------------------------------------------
# Test cases
# ---------------------------------------------------------------------------

TEST_CASES = [
    {
        "name": "ivt_stub",
        "input": "设 f 是连续函数，对于所有x，如果f(x)等于0则x大于0",
        "expected_fragments": [
            "import Mathlib",
            "theorem ivt_stub",
            "{f : ℝ → ℝ} (hf : Continuous f)",
            "∀ x,",
            "f x = 0 → x > 0",
            "sorry",
        ],
    },
    {
        "name": "mvt_stub",
        "input": "设 f 是可微函数，f 在 [a,b] 上连续，f 在 (a,b) 上可微，则存在 c 使得 f(b) - f(a) 等于 f'(c) * (b - a)",
        "expected_fragments": [
            "import Mathlib",
            "theorem mvt_stub",
            "{f : ℝ → ℝ} (hf : Differentiable ℝ f)",
            "ContinuousOn f (Icc a b)",
            "DifferentiableOn ℝ f (Ioo a b)",
            "∃ c,",
            "sorry",
        ],
    },
    {
        "name": "monotone_convergence",
        "input": "设 a_n 是单调递增数列且有上界，则 a_n 收敛",
        "expected_fragments": [
            "import Mathlib",
            "theorem monotone_convergence",
            "sorry",
        ],
    },
    {
        "name": "lagrange",
        "input": "设 G 是有限群，H 是 G 的子群，则 H 的阶整除 G 的阶",
        "expected_fragments": [
            "import Mathlib",
            "theorem lagrange",
            "{G : Type*} [Group G] [Fintype G]",
            "sorry",
        ],
    },
    {
        "name": "factor_theorem",
        "input": "设 F 是域，p 是 F 上的多项式，如果 a 属于 F 且 p(a) 等于 0，则存在 q 使得 p(x) 等于 (x - a) * q(x)",
        "expected_fragments": [
            "import Mathlib",
            "theorem factor_theorem",
            "{F : Type*} [Field F]",
            "sorry",
        ],
    },
    {
        "name": "abelian_center",
        "input": "设 G 是交换群，则对于所有 g 属于 G，g 属于 G 的中心",
        "expected_fragments": [
            "import Mathlib",
            "theorem abelian_center",
            "{G : Type*} [CommGroup G]",
            "sorry",
        ],
    },
    {
        "name": "triangle_inequality",
        "input": "设 X 是度量空间，对于所有 x y z 属于 X，d(x,z) 小于等于 d(x,y) + d(y,z)",
        "expected_fragments": [
            "import Mathlib",
            "theorem triangle_inequality",
            "{X : Type*} [MetricSpace X]",
            "sorry",
        ],
    },
    {
        "name": "convex_set",
        "input": "设 S 是凸集，对于所有 x y 属于 S 和所有 t 属于 [0,1]，(1-t)*x + t*y 属于 S",
        "expected_fragments": [
            "import Mathlib",
            "theorem convex_set",
            "sorry",
        ],
    },
    {
        "name": "fermat_little",
        "input": "设 p 是素数，a 是整数，如果 a 不被 p 整除，则 a^(p-1) 模 p 等于 1",
        "expected_fragments": [
            "import Mathlib",
            "theorem fermat_little",
            "sorry",
        ],
    },
    {
        "name": "gcd_exists",
        "input": "设 a b 是自然数，则存在 d 使得 d 整除 a 且 d 整除 b 且对于所有 e 如果 e 整除 a 且 e 整除 b 则 e 小于等于 d",
        "expected_fragments": [
            "import Mathlib",
            "theorem gcd_exists",
            "sorry",
        ],
    },
]


# ---------------------------------------------------------------------------
# Validation helpers
# ---------------------------------------------------------------------------

def validate_syntax(code: str) -> List[str]:
    """Perform lightweight syntactic checks on generated Lean code."""
    errors = []

    lines = code.splitlines()

    # Must start with import
    if not lines or not lines[0].startswith("import "):
        errors.append("Missing or malformed import statement")

    # Must contain a theorem declaration
    if not any(re.match(r"^theorem\s+\w+", line) for line in lines):
        errors.append("Missing theorem declaration")

    # Must end with sorry
    if "sorry" not in code:
        errors.append("Missing 'sorry' placeholder")

    # Check for unbalanced parentheses / braces (basic)
    for opener, closer in [("(", ")"), ("{", "}"), ("[", "]")]:
        if code.count(opener) != code.count(closer):
            errors.append(f"Unbalanced {opener}/{closer}")

    # Check for stray Chinese punctuation that might break parsing
    forbidden = ["，", "。", "；", "：", "、"]
    for char in forbidden:
        if char in code:
            # Only flag if outside a comment
            # Simple heuristic: check each line
            for line in lines:
                if char in line and not line.strip().startswith("/-") and not line.strip().startswith("--"):
                    errors.append(f"Stray Chinese punctuation '{char}' in code")
                    break

    return errors


# ---------------------------------------------------------------------------
# Test runner
# ---------------------------------------------------------------------------

def run_tests() -> bool:
    passed = 0
    failed = 0

    print("=" * 60)
    print("AI Formalizer Test Suite")
    print("=" * 60)

    for case in TEST_CASES:
        name = case["name"]
        stmt = case["input"]
        frags = case["expected_fragments"]

        code = formalize(stmt, name)

        # Check fragments
        missing = [f for f in frags if f not in code]

        # Check syntax
        syntax_errors = validate_syntax(code)

        if missing or syntax_errors:
            failed += 1
            print(f"\n[FAIL] {name}")
            if missing:
                print(f"  Missing fragments: {missing}")
            if syntax_errors:
                print(f"  Syntax errors: {syntax_errors}")
            print(f"  Generated code:\n{code}")
        else:
            passed += 1
            print(f"[PASS] {name}")

    print("\n" + "=" * 60)
    print(f"Results: {passed} passed, {failed} failed out of {len(TEST_CASES)}")
    print("=" * 60)

    return failed == 0


if __name__ == "__main__":
    ok = run_tests()
    sys.exit(0 if ok else 1)
