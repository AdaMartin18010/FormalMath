import json
import os
import re
from pathlib import Path

LEAN_DIR = Path("e:/_src/FormalMath/FormalMath-Enhanced/lean4/FormalMath/FormalMath")
OUTPUT_JSON = Path("e:/_src/FormalMath/tools/lean_stats.json")

# Heuristic domain mapping from filename keywords
DOMAIN_MAP = {
    "Algebra": ["Algebra", "Group", "Ring", "Field", "Module", "Commutative", "Noetherian", "Ideal", "Galois", "Character", "Representation", "UniversalEnveloping"],
    "代数几何": ["AlgebraicGeometry", "Scheme", "Sheaf", "Cohomology", "Chern", "Motive", "Faltings", "Mordell", "Elliptic", "ArithmeticGeometry", "Moduli", "Perfectoid", "DerivedAlgebraic"],
    "数论": ["NumberTheory", "Prime", "QuadraticReciprocity", "ChineseRemainder", "Fermat", "Wilson", "Infinitude", "Euclidean", "PrimitiveRoot", "RootsOfUnity", "Modular", "Taniyama", "Weil", "Birch", "p-adic", "ClassField"],
    "分析": ["Analysis", "MeanValue", "Bolzano", "IntermediateValue", "HeineBorel", "InverseFunction", "ImplicitFunction", "Taylor", "UniformConvergence", "ImproperIntegral", "Complex", "Fourier", "Fejer", "Plancherel", "Functional", "HahnBanach", "Riesz", "LaxMilgram", "Measure", "Lebesgue", "RadonNikodym", "AM_GM", "CauchySchwarz", "Holder", "Minkowski", "Young", "Sobolev", "Distribution", "CalculusOfVariations", "Green", "Divergence", "Stokes"],
    "拓扑": ["Topology", "Compactness", "Tychonoff", "Urysohn", "Tietze", "Brouwer", "HairyBall", "Sard", "Morse", "CoveringSpace", "FundamentalGroup", "Homotopy", "Homological", "Knot", "LowDimensional", "GeometricTopology", "Poincare", "Jordan"],
    "微分几何": ["Manifold", "Curvature", "Geodesic", "Connection", "PrincipalBundle", "Riemann", "Symplectic", "ComplexGeometry", "IndexTheorem", "Hodge", "Mirror"],
    "概率统计": ["Probability", "Statistics", "CentralLimit", "LawOfLarge", "Markov", "Martingale", "RandomMatrix", "Information", "MaximumLikelihood", "Stochastic"],
    "微分方程": ["PDE", "HeatEquation", "WaveEquation", "NavierStokes", "EllipticPDE", "WeakSolution", "PicardLindelof"],
    "逻辑与基础": ["Logic", "Completeness", "ProofTheory", "Computability", "SetTheory", "Zorn", "Cantor", "WellOrdering", "TypeTheory", "HomotopyTypeTheory", "Topos", "Univalent", "ModelTheory", "MathematicalPhilosophy"],
    "动力系统/遍历论": ["Dynamical", "Ergodic"],
    "组合/图论": ["Combinatorics", "Graph", "Ramsey", "Pigeonhole"],
    "算法/复杂度": ["Algorithm", "Complexity", "PvsNP", "Cryptography", "Optimization", "OperationsResearch", "Numerical", "MachineLearning", "DeepLearning", "ReinforcementLearning", "Control"],
    "物理/其他应用": ["Physics", "Quantum", "String", "GeneralRelativity", "YangMills", "VertexOperator", "QuantumField", "StatisticalMechanics", "Finance", "Economics", "GameTheory", "Biology"],
    "范畴论/高级结构": ["CategoryTheory", "FunctorCategory", "HigherCategory", "DerivedFunctor"],
    "Mathlib基础": ["Mathlib"],
}

def guess_domain(filename):
    base = Path(filename).stem
    for domain, keywords in DOMAIN_MAP.items():
        for kw in keywords:
            if kw.lower() in base.lower():
                return domain
    return "其他"

def extract_theorems(content):
    # Count theorem/lemma declarations (not in comments)
    # A simple heuristic: count lines starting with theorem/lemma or theorem/lemma after whitespace
    theorem_pattern = re.compile(r'^\s*(?:theorem|lemma)\s+(\w+)', re.MULTILINE)
    theorems = theorem_pattern.findall(content)
    return theorems

def extract_sorrys(content):
    # Count occurrences of \bsorry\b outside string literals is hard; we do a simple count.
    # Exclude lines that are pure comments containing sorry? Often comments also mark sorry.
    # We'll count all \bsorry\b tokens, but subtract those that appear after `--` on the same line.
    sorry_pattern = re.compile(r'\bsorry\b')
    comment_pattern = re.compile(r'--.*?\bsorry\b')
    block_comment_pattern = re.compile(r'/\-.*?\-\/', re.DOTALL)
    
    total_sorry = len(sorry_pattern.findall(content))
    comment_sorry = len(comment_pattern.findall(content))
    # block comments
    block_comments = block_comment_pattern.findall(content)
    block_sorry = sum(len(sorry_pattern.findall(bc)) for bc in block_comments)
    
    return total_sorry - comment_sorry - block_sorry

def extract_mathlib_refs(content):
    # Look for patterns like `Mathlib.X.Y` or lines containing Mathlib4对应
    lines = content.splitlines()
    refs = []
    for line in lines[:30]:  # top 30 lines
        m = re.search(r'`(Mathlib[.\w]+)`', line)
        if m:
            refs.append(m.group(1))
    # Also search in first 500 chars for any explicit mentions
    for m in re.finditer(r'`(Mathlib[.\w]+)`', content[:800]):
        refs.append(m.group(1))
    return list(dict.fromkeys(refs))  # preserve order, remove dups

def classify(sorry_count, theorem_count):
    if theorem_count == 0:
        if sorry_count == 0:
            return "A"
        else:
            return "C"
    ratio = sorry_count / theorem_count
    if sorry_count == 0 or ratio < 0.10:
        return "A"
    elif ratio <= 0.50:
        return "B"
    else:
        return "C"

def main():
    files = sorted(LEAN_DIR.rglob("*.lean"))
    results = []
    for f in files:
        rel = f.relative_to(LEAN_DIR).as_posix()
        content = f.read_text(encoding='utf-8')
        theorems = extract_theorems(content)
        theorem_count = len(theorems)
        sorry_count = extract_sorrys(content)
        category = classify(sorry_count, theorem_count)
        mathlib_refs = extract_mathlib_refs(content)
        domain = guess_domain(f.name)
        
        results.append({
            "file": rel,
            "filename": f.name,
            "theorem_count": theorem_count,
            "sorry_count": sorry_count,
            "category": category,
            "domain": domain,
            "mathlib_refs": mathlib_refs,
            "theorem_names": theorems[:10],  # first 10 names
        })
    
    OUTPUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT_JSON, "w", encoding="utf-8") as out:
        json.dump(results, out, ensure_ascii=False, indent=2)
    
    print(f"Scanned {len(results)} files. JSON written to {OUTPUT_JSON}")
    counts = {"A": 0, "B": 0, "C": 0}
    for r in results:
        counts[r["category"]] += 1
    print(f"A: {counts['A']}, B: {counts['B']}, C: {counts['C']}")

if __name__ == "__main__":
    main()
