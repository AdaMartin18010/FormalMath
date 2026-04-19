"""
AI Formalizer Core Engine
Convert natural language mathematical statements to Lean 4 code stubs.
Uses rule-based pattern matching (no external AI model required).
Supports Chinese and English inputs.
"""

import re
from typing import List, Tuple


# ---------------------------------------------------------------------------
# Translation tables: Chinese / English keywords -> Lean 4 tokens
# ---------------------------------------------------------------------------

QUANTIFIERS = [
    # quantifier + "belongs to" combos (must come before standalone quantifiers)
    (r"对于所有\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+属于\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*，?\s*", r"∀ \1 ∈ \2, "),
    (r"for all\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+in\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*,?\s*", r"∀ \1 ∈ \2, "),
    (r"forall\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+in\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*,?\s*", r"∀ \1 ∈ \2, "),
    (r"对于任意\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+属于\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*，?\s*", r"∀ \1 ∈ \2, "),
    (r"存在\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+属于\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+使得\s*", r"∃ \1 ∈ \2, "),
    (r"exists\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+in\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+s\.t\.\s*", r"∃ \1 ∈ \2, "),
    (r"exists\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+in\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+such that\s*", r"∃ \1 ∈ \2, "),
    # standalone quantifiers
    (r"对于所有\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*，?\s*", r"∀ \1, "),
    (r"forall\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*,?\s*", r"∀ \1, "),
    (r"对于任意\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*，?\s*", r"∀ \1, "),
    (r"for all\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*,?\s*", r"∀ \1, "),
    (r"存在\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*使得\s*", r"∃ \1, "),
    (r"\bexists\b\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+s\.t\.\s*", r"∃ \1, "),
    (r"\bexists\b\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+such that\s*", r"∃ \1, "),
]

LOGIC = [
    (r"如果\s*", r""),
    (r"则\s*", r"→ "),
    (r"那么\s*", r"→ "),
    (r"且\s*", r"∧ "),
    (r"并且\s*", r"∧ "),
    (r"或\s*", r"∨ "),
    (r"或者\s*", r"∨ "),
    (r"非\s*", r"¬"),
    (r"不是\s*", r"¬"),
    (r"蕴含\s*", r"→ "),
    (r"等价于\s*", r"↔ "),
    (r"当且仅当\s*", r"↔ "),
    (r"\bif\b\s*", r""),
    (r"\bthen\b\s*", r"→ "),
    (r"\band\b\s*", r"∧ "),
    (r"\bor\b\s*", r"∨ "),
    (r"\bnot\b\s*", r"¬"),
    (r"\bimplies\b\s*", r"→ "),
    (r"\biff\b\s*", r"↔ "),
]

RELATIONS = [
    (r"等于\s*", r" = "),
    (r"不等于\s*", r" ≠ "),
    (r"大于等于\s*", r" ≥ "),
    (r"小于等于\s*", r" ≤ "),
    (r"大于\s*", r" > "),
    (r"小于\s*", r" < "),
    (r"属于\s*", r" ∈ "),
    (r"不属于\s*", r" ∉ "),
    (r"包含于\s*", r" ⊆ "),
    (r"包含\s*", r" ⊇ "),
    (r"是\s*的子集\s*", r" ⊆ "),
    (r"是\s*的元素\s*", r" ∈ "),
    (r"([a-zA-Z_][a-zA-Z0-9_]*)\s+不\s+被\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+整除", r"¬(\2 ∣ \1)"),
    (r"([a-zA-Z_][a-zA-Z0-9_]*)\s+被\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+整除", r"\2 ∣ \1"),
    (r"整除\s*", r" ∣ "),
]

FUNCTIONS = [
    (r"([a-zA-Z_][a-zA-Z0-9_]*)\s*在\s*\[([^\]]+)\]\s*上连续", r"ContinuousOn \1 (Icc \2)"),
    (r"([a-zA-Z_][a-zA-Z0-9_]*)\s*在\s*\(([^)]+)\)\s*上可微", r"DifferentiableOn ℝ \1 (Ioo \2)"),
    (r"([a-zA-Z_][a-zA-Z0-9_]*)\s*在\s*\[([^\]]+)\]\s*上可积", r"IntegrableOn \1 (Icc \2)"),
    (r"([a-zA-Z_][a-zA-Z0-9_]*)\s*在\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*处可微", r"DifferentiableAt ℝ \1 \2"),
    (r"([a-zA-Z_][a-zA-Z0-9_]*)\s*在\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*处连续", r"ContinuousAt \1 \2"),
    (r"([a-zA-Z_][a-zA-Z0-9_]*)\s*is continuous on\s*\[([^\]]+)\]", r"ContinuousOn \1 (Icc \2)"),
    (r"([a-zA-Z_][a-zA-Z0-9_]*)\s*is differentiable on\s*\(([^)]+)\)", r"DifferentiableOn ℝ \1 (Ioo \2)"),
    (r"([a-zA-Z_][a-zA-Z0-9_]*)\s*is integrable on\s*\[([^\]]+)\]", r"IntegrableOn \1 (Icc \2)"),
    (r"([a-zA-Z_][a-zA-Z0-9_]*)\s*is differentiable at\s+([a-zA-Z_][a-zA-Z0-9_]*)", r"DifferentiableAt ℝ \1 \2"),
    (r"([a-zA-Z_][a-zA-Z0-9_]*)\s*is continuous at\s+([a-zA-Z_][a-zA-Z0-9_]*)", r"ContinuousAt \1 \2"),
]

ASSUMPTIONS = [
    (r"设\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+是连续函数", r"{\1 : ℝ → ℝ} (h\1 : Continuous \1)"),
    (r"设\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+是可微函数", r"{\1 : ℝ → ℝ} (h\1 : Differentiable ℝ \1)"),
    (r"设\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+是有限群", r"{\1 : Type*} [Group \1] [Fintype \1]"),
    (r"设\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+是交换群", r"{\1 : Type*} [CommGroup \1]"),
    (r"设\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+是域", r"{\1 : Type*} [Field \1]"),
    (r"设\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+是环", r"{\1 : Type*} [Ring \1]"),
    (r"设\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+是拓扑空间", r"{\1 : Type*} [TopologicalSpace \1]"),
    (r"设\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+是度量空间", r"{\1 : Type*} [MetricSpace \1]"),
    (r"设\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+是凸集", r"{S : Set (EuclideanSpace ℝ (Fin n))} (hS : Convex ℝ S)"),
    (r"设\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+是素数", r"{\1 : ℕ} (h\1 : Nat.Prime \1)"),
    (r"设\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+是整数", r"{\1 : ℤ}"),
    (r"([a-zA-Z_][a-zA-Z0-9_]*)\s+是\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+的子群", r"{\1 : Subgroup \2}"),
    (r"let\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+be a continuous function", r"{\1 : ℝ → ℝ} (h\1 : Continuous \1)"),
    (r"let\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+be a differentiable function", r"{\1 : ℝ → ℝ} (h\1 : Differentiable ℝ \1)"),
    (r"let\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+be a finite group", r"{\1 : Type*} [Group \1] [Fintype \1]"),
    (r"let\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+be an abelian group", r"{\1 : Type*} [CommGroup \1]"),
    (r"let\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+be a field", r"{\1 : Type*} [Field \1]"),
    (r"let\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+be a ring", r"{\1 : Type*} [Ring \1]"),
    (r"let\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+be a topological space", r"{\1 : Type*} [TopologicalSpace \1]"),
    (r"let\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+be a metric space", r"{\1 : Type*} [MetricSpace \1]"),
]

SPECIAL_SYMBOLS = [
    (r"收敛到\s*", r" → "),
    (r"converges to\s*", r" → "),
    (r"极限是\s*", r" → "),
    (r"limit is\s*", r" → "),
    (r"映射到\s*", r" ↦ "),
    (r"maps to\s*", r" ↦ "),
    (r"无穷大\s*", r"∞"),
    (r"infinity\s*", r"∞"),
    (r"正无穷\s*", r"+∞"),
    (r"负无穷\s*", r"-∞"),
    (r"实数集\s*", r"ℝ"),
    (r"real numbers\s*", r"ℝ"),
    (r"自然数集\s*", r"ℕ"),
    (r"natural numbers\s*", r"ℕ"),
    (r"整数集\s*", r"ℤ"),
    (r"integers\s*", r"ℤ"),
    (r"有理数集\s*", r"ℚ"),
    (r"rational numbers\s*", r"ℚ"),
    (r"复数集\s*", r"ℂ"),
    (r"complex numbers\s*", r"ℂ"),
]

CONCLUSION_PATTERNS = [
    (r"证明\s*", r""),
    (r"prove\s*", r""),
    (r"show\s*", r""),
    (r"证明\s*那\s*", r""),
    (r"prove that\s*", r""),
    (r"show that\s*", r""),
    (r"求证\s*", r""),
    (r"需要证明\s*", r""),
]

# ---------------------------------------------------------------------------
# Helper utilities
# ---------------------------------------------------------------------------

def _apply_rules(text: str, rules: List[Tuple[str, str]]) -> str:
    """Sequentially apply regex substitution rules."""
    for pattern, repl in rules:
        text = re.sub(pattern, repl, text, flags=re.IGNORECASE)
    return text


def _smart_split(text: str, delimiters: str = "，,;；") -> List[str]:
    """
    Split text by delimiters but ignore delimiters inside parentheses,
    brackets, and braces.
    """
    parts = []
    current = []
    depth_paren = 0
    depth_bracket = 0
    depth_brace = 0

    for ch in text:
        if ch == '(':
            depth_paren += 1
        elif ch == ')':
            depth_paren -= 1
        elif ch == '[':
            depth_bracket += 1
        elif ch == ']':
            depth_bracket -= 1
        elif ch == '{':
            depth_brace += 1
        elif ch == '}':
            depth_brace -= 1
        elif ch in delimiters and depth_paren == 0 and depth_bracket == 0 and depth_brace == 0:
            part = "".join(current).strip()
            if part:
                parts.append(part)
            current = []
            continue
        current.append(ch)

    part = "".join(current).strip()
    if part:
        parts.append(part)

    return parts


def _split_assumptions(text: str) -> Tuple[List[str], str]:
    """
    Split a statement into assumption clauses and conclusion.
    Returns (assumptions, conclusion).
    """
    # Try to split on common conclusion separators
    separators = [
        r"，则",
        r", then",
        r"，那么",
        r", 那么",
        r"; then",
        r"，因此",
        r", therefore",
        r"，所以",
    ]
    for sep in separators:
        match = re.split(sep, text, maxsplit=1, flags=re.IGNORECASE)
        if len(match) == 2:
            assumptions = _smart_split(match[0])
            conclusion = match[1].strip()
            return assumptions, conclusion

    # No explicit separator found.
    # If the text starts with an assumption keyword (设 / let),
    # try to split after the first assumption clause.
    text_stripped = text.strip()
    if text_stripped.startswith("设") or text_stripped.lower().startswith("let "):
        # Try to find where the first assumption ends and the statement begins.
        # Heuristic: look for the first standalone comma after a complete
        # assumption pattern, or before a quantifier.
        all_assumptions = _smart_split(text_stripped)
        if len(all_assumptions) > 1:
            # Check if the first clause is an assumption pattern
            first = all_assumptions[0]
            is_assumption = any(
                re.search(pat, first, re.IGNORECASE) for pat, _ in ASSUMPTIONS
            )
            if is_assumption:
                return [first], " ".join(all_assumptions[1:])
            # Otherwise check if any clause is an assumption
            assumption_clauses = []
            remaining = []
            for clause in all_assumptions:
                is_assump = any(
                    re.search(pat, clause, re.IGNORECASE) for pat, _ in ASSUMPTIONS
                )
                if is_assump:
                    assumption_clauses.append(clause)
                else:
                    remaining.append(clause)
            if assumption_clauses and remaining:
                return assumption_clauses, " ".join(remaining)

    # Fallback: treat the whole thing as conclusion
    return [], text.strip()


def _extract_assumptions(assumptions: List[str]) -> Tuple[List[str], List[str]]:
    """
    Given a list of assumption strings, return:
      - list of Lean parameter declarations
      - list of remaining hypothesis expressions
    """
    params: List[str] = []
    hyps: List[str] = []

    for assumption in assumptions:
        matched = False
        for pattern, repl in ASSUMPTIONS:
            if re.search(pattern, assumption, re.IGNORECASE):
                params.append(re.sub(pattern, repl, assumption, flags=re.IGNORECASE))
                matched = True
                break
        if not matched:
            # Translate the assumption to Lean expression
            lean_expr = _translate_expr(assumption)
            hyps.append(lean_expr)

    return params, hyps


def _translate_expr(expr: str) -> str:
    """Translate a single mathematical expression to Lean syntax."""
    # Replace common algebraic / number-theory phrases before symbol translation
    expr = re.sub(r'([a-zA-Z_][a-zA-Z0-9_]*)\s+的阶', r'Nat.card \1', expr)
    expr = re.sub(r'模\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+等于', r'≡ [ZMOD \1] ', expr)
    expr = re.sub(r'模\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*', r'[ZMOD \1] ', expr)

    # Function application: f(x) -> f x (Lean style) — do this early
    # so that subsequent rules see Lean-style function applications.
    expr = re.sub(r'([a-zA-Z_][a-zA-Z0-9_]*)\s*\(([^()]+)\)', r'\1 \2', expr)

    # Apply function patterns (continuous, differentiable, etc.)
    for pattern, repl in FUNCTIONS:
        expr = re.sub(pattern, repl, expr, flags=re.IGNORECASE)

    # Apply quantifiers
    expr = _apply_rules(expr, QUANTIFIERS)

    # Apply logic operators
    expr = _apply_rules(expr, LOGIC)

    # Apply relations
    expr = _apply_rules(expr, RELATIONS)

    # Apply special symbols
    expr = _apply_rules(expr, SPECIAL_SYMBOLS)

    # Clean up multiple spaces
    expr = re.sub(r"\s+", " ", expr).strip()

    # Replace remaining Chinese punctuation with ASCII equivalents or remove
    expr = expr.replace("，", ", ").replace("；", "; ")
    expr = expr.replace("。", ". ")

    # Convert commas inside Lean parentheses to spaces for cleaner syntax
    # e.g. (Icc a,b) -> (Icc a b)
    expr = re.sub(r'\(([^()]*?),\s*([^()]*?)\)', r'(\1 \2)', expr)

    # Normalize spaces around binary operators
    expr = re.sub(r'\s*([→↔∧∨∈∉⊆⊇≥≤≠=<>+\-*/])\s*', r' \1 ', expr)
    expr = re.sub(r"\s+", " ", expr).strip()

    return expr


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def formalize(statement: str, theorem_name: str = "thm") -> str:
    """
    Convert a natural-language mathematical statement into a Lean 4 theorem stub.
    """
    # Preprocess: remove conclusion keywords
    for pattern, repl in CONCLUSION_PATTERNS:
        statement = re.sub(pattern, repl, statement, flags=re.IGNORECASE)

    statement = statement.strip()

    # Split into assumptions and conclusion
    assumptions, conclusion = _split_assumptions(statement)

    # Extract structured parameters and remaining hypotheses
    params, hyps = _extract_assumptions(assumptions)

    # Translate conclusion
    lean_conclusion = _translate_expr(conclusion)

    # Build the theorem statement
    lines = []
    lines.append("import Mathlib")
    lines.append("")

    # Build theorem declaration
    theorem_line = f"theorem {theorem_name}"

    # Add parameters
    for param in params:
        theorem_line += f" {param}"

    # Add hypotheses
    for i, hyp in enumerate(hyps):
        theorem_line += f" (h{i+1} : {hyp})"

    # Add conclusion
    theorem_line += f" : {lean_conclusion} := by"
    lines.append(theorem_line)
    lines.append("  sorry")
    lines.append("")

    return "\n".join(lines)


def formalize_simple(statement: str, theorem_name: str = "thm") -> str:
    """
    Simplified version that does not attempt assumption splitting;
    translates the whole statement in one pass.
    """
    for pattern, repl in CONCLUSION_PATTERNS:
        statement = re.sub(pattern, repl, statement, flags=re.IGNORECASE)

    lean_stmt = _translate_expr(statement.strip())

    lines = []
    lines.append("import Mathlib")
    lines.append("")
    lines.append(f"theorem {theorem_name} : {lean_stmt} := by")
    lines.append("  sorry")
    lines.append("")

    return "\n".join(lines)


def formalize_with_doc(statement: str, theorem_name: str = "thm", doc: str = "") -> str:
    """
    Generate a theorem with a docstring comment.
    """
    code = formalize(statement, theorem_name)
    doc_comment = f"/-\n  {doc or statement}\n-/\n"
    parts = code.split("\n")
    result = "\n".join(parts[:2] + [doc_comment + parts[2]] + parts[3:])
    return result
