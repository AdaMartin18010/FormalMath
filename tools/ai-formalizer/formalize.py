"""
AI Formalizer Batch Processor
Reads Markdown files containing theorem statements, generates Lean 4 code
stubs, and inserts them back into the document.

Usage:
    python formalize.py <input.md> [output.md]
    python formalize.py --batch <dir> [--pattern "*.md"]
"""

import sys
import os
import re
import argparse
import glob

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from core import formalize, formalize_with_doc


# ---------------------------------------------------------------------------
# Markdown parsing helpers
# ---------------------------------------------------------------------------

THEOREM_BLOCK_PATTERN = re.compile(
    r"```\s*theorem\s*\n"
    r"(.*?)"
    r"```",
    re.DOTALL,
)

NATURAL_LANG_PATTERN = re.compile(
    r"```\s*natural\s*\n"
    r"(.*?)"
    r"```",
    re.DOTALL,
)


# ---------------------------------------------------------------------------
# Core processing logic
# ---------------------------------------------------------------------------

def generate_theorem_stub(statement: str, name_hint: str = "thm") -> str:
    """Generate a fenced Lean 4 code block from a natural-language statement."""
    # Derive a theorem name from the first few words if no hint given
    theorem_name = name_hint
    if theorem_name == "thm":
        # Try to extract a name from the statement
        words = re.findall(r"[a-zA-Z_][a-zA-Z0-9_]*", statement)
        if words:
            theorem_name = words[0] + "_thm"

    code = formalize(statement.strip(), theorem_name)
    return f"```lean4\n{code}```\n"


def process_markdown(text: str) -> str:
    """
    Scan a Markdown document for natural-language theorem blocks
    and insert generated Lean 4 stubs.

    Supported block types:
      ```natural
      <statement>
      ```
    Replaced with:
      ```lean4
      <generated code>
      ```
    """
    def replacer(match: re.Match) -> str:
        statement = match.group(1).strip()
        stub = generate_theorem_stub(statement)
        return stub

    return NATURAL_LANG_PATTERN.sub(replacer, text)


def process_file(input_path: str, output_path: str | None = None) -> str:
    """Read a Markdown file, formalize natural blocks, write result."""
    with open(input_path, "r", encoding="utf-8") as f:
        content = f.read()

    transformed = process_markdown(content)

    if output_path:
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(transformed)
        print(f"Written: {output_path}")
    else:
        # Overwrite in-place
        with open(input_path, "w", encoding="utf-8") as f:
            f.write(transformed)
        print(f"Updated in-place: {input_path}")

    return transformed


def batch_process(directory: str, pattern: str = "*.md") -> int:
    """Process all matching Markdown files in a directory (recursively)."""
    search_path = os.path.join(directory, "**", pattern)
    files = glob.glob(search_path, recursive=True)

    if not files:
        print(f"No files matched pattern '{pattern}' in {directory}")
        return 0

    processed = 0
    for filepath in files:
        # Skip files inside node_modules, .git, etc.
        if any(part.startswith(".") for part in filepath.split(os.sep)):
            continue
        try:
            process_file(filepath)
            processed += 1
        except Exception as e:
            print(f"Error processing {filepath}: {e}")

    print(f"\nBatch complete: {processed} file(s) processed.")
    return processed


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Batch formalizer: convert natural-language theorem blocks in Markdown to Lean 4 stubs."
    )
    parser.add_argument("input", nargs="?", help="Input Markdown file or directory")
    parser.add_argument("-o", "--output", help="Output file (default: overwrite input)")
    parser.add_argument("-b", "--batch", action="store_true", help="Process all Markdown files in directory recursively")
    parser.add_argument("-p", "--pattern", default="*.md", help="File glob pattern for batch mode")
    parser.add_argument("--stdin", action="store_true", help="Read Markdown from stdin")

    args = parser.parse_args()

    if args.stdin:
        text = sys.stdin.read()
        result = process_markdown(text)
        print(result)
        return

    if not args.input:
        parser.print_help()
        sys.exit(1)

    if args.batch:
        batch_process(args.input, args.pattern)
    else:
        if not os.path.isfile(args.input):
            print(f"Error: {args.input} is not a file. Use --batch for directories.")
            sys.exit(1)
        process_file(args.input, args.output)


if __name__ == "__main__":
    main()
