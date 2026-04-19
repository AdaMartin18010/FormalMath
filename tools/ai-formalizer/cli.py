"""
AI Formalizer CLI
Interactive command-line interface for converting natural-language math
statements into Lean 4 code stubs.
"""

import sys
import os

# Allow importing core.py from the same directory
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from core import formalize, formalize_simple


BANNER = """
╔══════════════════════════════════════════════════════════════════╗
║           FormalMath AI Formalizer (Prototype)                   ║
║   Natural Language → Lean 4 Theorem Stubs (Rule-based)           ║
╠══════════════════════════════════════════════════════════════════╣
║  输入自然语言数学定理描述，生成 Lean 4 代码框架。                  ║
║  Enter a natural-language theorem, get a Lean 4 stub.            ║
╚══════════════════════════════════════════════════════════════════╝
"""

PROMPT = " formalizer > "


def main() -> None:
    print(BANNER)
    print("Commands:")
    print("  :q, :quit          Exit the program")
    print("  :simple <stmt>     Use simple mode (no assumption splitting)")
    print("  :name <name>       Set theorem name for next input")
    print("  :help              Show this help message")
    print("")

    theorem_name = "thm"

    while True:
        try:
            user_input = input(PROMPT).strip()
        except (EOFError, KeyboardInterrupt):
            print("\nBye!")
            break

        if not user_input:
            continue

        # Commands
        if user_input.lower() in (":q", ":quit"):
            print("Bye!")
            break

        if user_input.lower() == ":help":
            print("Commands:")
            print("  :q, :quit          Exit")
            print("  :simple <stmt>     Simple mode")
            print("  :name <name>       Set theorem name")
            print("")
            continue

        if user_input.lower().startswith(":name "):
            theorem_name = user_input[6:].strip()
            print(f"  [Theorem name set to '{theorem_name}']")
            continue

        if user_input.lower().startswith(":simple "):
            stmt = user_input[8:].strip()
            code = formalize_simple(stmt, theorem_name)
            print("\n--- Generated Lean 4 Code ---")
            print(code)
            print("-------------------------------\n")
            continue

        # Default: use formalize
        code = formalize(user_input, theorem_name)
        print("\n--- Generated Lean 4 Code ---")
        print(code)
        print("-------------------------------\n")


if __name__ == "__main__":
    main()
