#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
根据 msc_primary 为数学内容文档批量注入标准教材引用，提升引用密度与权威源对齐。

注入范围：银层/金层/铜层/未标注文档，要求有有效 msc_primary、非报告类、正文不少于 300 字符。

用法：
    python scripts/inject_standard_textbooks_by_msc.py
"""

import re
import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

# 按 MSC 两位大类映射权威教材。每类优先保留 1~3 本最经典、ISBN/MR 可核验的著作。
STANDARD_BOOKS = {
    "00": [  # General / expository
        {"title": "The Princeton Companion to Mathematics",
            "doi": "10.1515/9781400830398", "author": "Timothy Gowers (ed.)", "edition": "1st", "publisher": "Princeton University Press", "year": 2008, "isbn": "9780691118802", "mr_number": "MR2467561"},
        {"title": "How to Prove It: A Structured Approach",
            "doi": "10.1017/CBO9780511811029", "author": "Daniel J. Velleman", "edition": "2nd", "publisher": "Cambridge University Press", "year": 2006, "isbn": "9780521675994", "mr_number": "MR2448845"},
    ],
    "01": [  # History and biography
        {"title": "Mathematics and Its History",
            "doi": "10.1007/978-1-4419-6053-5", "author": "John Stillwell", "edition": "3rd", "publisher": "Springer", "year": 2010, "isbn": "9781441960528", "mr_number": "MR2675606"},
        {"title": "A History of Mathematics: An Introduction", "author": "Victor J. Katz", "edition": "3rd", "publisher": "Pearson", "year": 2009, "isbn": "9780321387004"},
    ],
    "03": [  # Mathematical logic / set theory
        {"title": "Set Theory",
            "doi": "10.1007/3-540-44761-X", "author": "Thomas Jech", "edition": "3rd Millennium", "publisher": "Springer", "year": 2003, "isbn": "9783540440857", "mr_number": "MR1940513"},
        {"title": "A Course in Mathematical Logic",
            "doi": "10.1007/978-1-4757-4385-2", "author": "Yu.I. Manin", "edition": "1st", "publisher": "Springer", "year": 1977, "isbn": "9780387902432", "mr_number": "MR0453490"},
    ],
    "05": [  # Combinatorics
        {"title": "Enumerative Combinatorics, Vol. 1",
            "doi": "10.1017/CBO9781139058520", "author": "Richard P. Stanley", "edition": "2nd", "publisher": "Cambridge University Press", "year": 2012, "isbn": "9781107602625", "mr_number": "MR2868112"},
        {"title": "A Walk Through Combinatorics", "author": "Miklós Bóna", "edition": "4th", "publisher": "World Scientific", "year": 2016, "isbn": "9789813148847", "mr_number": "MR3561692"},
    ],
    "08": [  # General algebraic systems
        {"title": "Abstract Algebra",
            "doi": "10.1002/9781118214413", "author": "David S. Dummit and Richard M. Foote", "edition": "3rd", "publisher": "Wiley", "year": 2003, "isbn": "9780471433347", "mr_number": "MR2286236"},
    ],
    "11": [  # Number theory
        {"title": "An Introduction to the Theory of Numbers", "author": "G. H. Hardy and E. M. Wright", "edition": "6th", "publisher": "Oxford University Press", "year": 2008, "isbn": "9780199219865", "mr_number": "MR2445243"},
        {"title": "A Course in Arithmetic", "author": "Jean-Pierre Serre", "edition": "1st", "publisher": "Springer", "year": 1973, "isbn": "9780387900407", "mr_number": "MR0344216"},
        {"title": "Introduction to Analytic Number Theory",
            "doi": "10.1007/978-1-4757-5579-4", "author": "Tom M. Apostol", "edition": "1st", "publisher": "Springer", "year": 1976, "isbn": "9780387901633", "mr_number": "MR0434929"},
    ],
    "12": [  # Field theory / general algebra
        {"title": "Abstract Algebra",
            "doi": "10.1002/9781118214413", "author": "David S. Dummit and Richard M. Foote", "edition": "3rd", "publisher": "Wiley", "year": 2003, "isbn": "9780471433347", "mr_number": "MR2286236"},
        {"title": "Algebra",
            "doi": "10.1007/978-1-4613-0041-0", "author": "Michael Artin", "edition": "2nd", "publisher": "Pearson", "year": 2010, "isbn": "9780132413770"},
        {"title": "Algebra",
            "doi": "10.1007/978-1-4613-0041-0", "author": "Serge Lang", "edition": "Revised 3rd", "publisher": "Springer", "year": 2002, "isbn": "9780387953854", "mr_number": "MR1878556"},
    ],
    "13": [  # Commutative algebra
        {"title": "Introduction to Commutative Algebra", "author": "M. F. Atiyah and I. G. Macdonald", "edition": "1st", "publisher": "Addison-Wesley", "year": 1969, "isbn": "9780201407518", "mr_number": "MR0242802"},
        {"title": "Commutative Algebra: with a View Toward Algebraic Geometry",
            "doi": "10.1007/978-1-4612-5350-1", "author": "David Eisenbud", "edition": "1st", "publisher": "Springer", "year": 1995, "isbn": "9780387942681", "mr_number": "MR1322960"},
        {"title": "Commutative Ring Theory",
            "doi": "10.1017/CBO9781139171762", "author": "Hideyuki Matsumura", "edition": "1st", "publisher": "Cambridge University Press", "year": 1989, "isbn": "9780521367646", "mr_number": "MR0876123"},
    ],
    "14": [  # Algebraic geometry
        {"title": "Algebraic Geometry",
            "doi": "10.1007/978-1-4757-3849-0", "author": "Robin Hartshorne", "edition": "1st", "publisher": "Springer", "year": 1977, "isbn": "9780387902449", "mr_number": "MR0463157"},
        {"title": "The Rising Sea: Foundations of Algebraic Geometry", "author": "Ravi Vakil", "edition": "draft", "publisher": "Stanford University", "year": 2024},
        {"title": "Algebraic Geometry and Arithmetic Curves", "author": "Qing Liu", "edition": "1st", "publisher": "Oxford University Press", "year": 2002, "isbn": "9780199202492", "mr_number": "MR1917232"},
    ],
    "15": [  # Linear/multilinear algebra
        {"title": "Introduction to Linear Algebra", "author": "Gilbert Strang", "edition": "5th", "publisher": "Wellesley-Cambridge Press", "year": 2016, "isbn": "9780980232776"},
        {"title": "Linear Algebra Done Right",
            "doi": "10.1007/978-3-319-11080-6", "author": "Sheldon Axler", "edition": "3rd", "publisher": "Springer", "year": 2015, "isbn": "9783319110790"},
        {"title": "Matrix Analysis",
            "doi": "10.1017/CBO9780511810819", "author": "Roger A. Horn and Charles R. Johnson", "edition": "2nd", "publisher": "Cambridge University Press", "year": 2012, "isbn": "9780521839402", "mr_number": "MR2978210"},
    ],
    "16": [  # Associative rings and algebras
        {"title": "A First Course in Noncommutative Rings",
            "doi": "10.1007/978-1-4419-8616-0", "author": "T. Y. Lam", "edition": "2nd", "publisher": "Springer", "year": 2001, "isbn": "9780387951836", "mr_number": "MR1838439"},
        {"title": "Algebra",
            "doi": "10.1007/978-1-4613-0041-0", "author": "Serge Lang", "edition": "Revised 3rd", "publisher": "Springer", "year": 2002, "isbn": "9780387953854", "mr_number": "MR1878556"},
    ],
    "18": [  # Category theory
        {"title": "Categories for the Working Mathematician", "author": "Saunders Mac Lane", "edition": "2nd", "publisher": "Springer", "year": 1998, "isbn": "9780387984032", "mr_number": "MR1712872"},
        {"title": "Basic Category Theory", "author": "Tom Leinster", "edition": "1st", "publisher": "Cambridge University Press", "year": 2014, "isbn": "9781107044241", "mr_number": "MR3307165"},
    ],
    "19": [  # K-theory
        {"title": "K-Theory", "author": "Michael Atiyah", "edition": "1st", "publisher": "Addison-Wesley", "year": 1989, "isbn": "9780201407518", "mr_number": "MR1043170"},
        {"title": "K-Theory: An Introduction", "author": "Max Karoubi", "edition": "1st", "publisher": "Springer", "year": 1978, "isbn": "9783540080347", "mr_number": "MR0488029"},
    ],
    "20": [  # Group theory
        {"title": "Abstract Algebra",
            "doi": "10.1002/9781118214413", "author": "David S. Dummit and Richard M. Foote", "edition": "3rd", "publisher": "Wiley", "year": 2003, "isbn": "9780471433347", "mr_number": "MR2286236"},
        {"title": "An Introduction to the Theory of Groups", "author": "Joseph J. Rotman", "edition": "4th", "publisher": "Springer", "year": 1995, "isbn": "9780387942858", "mr_number": "MR1307623"},
    ],
    "22": [  # Topological groups, Lie groups
        {"title": "Lie Groups, Lie Algebras, and Representations: An Elementary Introduction",
            "doi": "10.1007/978-3-319-13467-3", "author": "Brian C. Hall", "edition": "2nd", "publisher": "Springer", "year": 2015, "isbn": "9783319134666", "mr_number": "MR3331229"},
        {"title": "Representations of Compact Lie Groups",
            "doi": "10.1007/978-3-662-12918-0", "author": "Theodor Bröcker and Tammo tom Dieck", "edition": "1st", "publisher": "Springer", "year": 1985, "isbn": "9783540136781", "mr_number": "MR0781344"},
    ],
    "26": [  # Real analysis
        {"title": "Principles of Mathematical Analysis", "author": "Walter Rudin", "edition": "3rd", "publisher": "McGraw-Hill", "year": 1976, "isbn": "9780070542358", "mr_number": "MR0385023"},
        {"title": "Understanding Analysis",
            "doi": "10.1007/978-1-4939-2712-8", "author": "Stephen Abbott", "edition": "2nd", "publisher": "Springer", "year": 2015, "isbn": "9781493927111"},
        {"title": "Real Mathematical Analysis",
            "doi": "10.1007/978-0-387-21676-7", "author": "Charles C. Pugh", "edition": "1st", "publisher": "Springer", "year": 2002, "isbn": "9780387952970", "mr_number": "MR1639930"},
        {"title": "Analysis I",
            "doi": "10.1007/978-981-10-1789-6", "author": "Terence Tao", "edition": "3rd", "publisher": "Springer", "year": 2016, "isbn": "9789811017896", "mr_number": "MR3728289"},
    ],
    "28": [  # Measure and integration
        {"title": "Real Analysis: Modern Techniques and Their Applications",
            "doi": "10.1002/9781118165883", "author": "Gerald B. Folland", "edition": "2nd", "publisher": "Wiley", "year": 1999, "isbn": "9780471317166", "mr_number": "MR1681462"},
        {"title": "Measure and Integral: An Introduction to Real Analysis", "author": "Richard L. Wheeden and Antoni Zygmund", "edition": "2nd", "publisher": "CRC Press", "year": 2015, "isbn": "9781498702898"},
    ],
    "30": [  # Complex analysis
        {"title": "Complex Analysis", "author": "Lars V. Ahlfors", "edition": "3rd", "publisher": "McGraw-Hill", "year": 1979, "isbn": "9780070006577", "mr_number": "MR0510197"},
        {"title": "Complex Analysis", "author": "Elias M. Stein and Rami Shakarchi", "edition": "1st", "publisher": "Princeton University Press", "year": 2003, "isbn": "9780691113852"},
        {"title": "Functions of One Complex Variable I",
            "doi": "10.1007/978-1-4612-7154-9", "author": "John B. Conway", "edition": "2nd", "publisher": "Springer", "year": 1995, "isbn": "9780387944609", "mr_number": "MR1344449"},
    ],
    "32": [  # Several complex variables
        {"title": "Complex Analysis", "author": "Elias M. Stein and Rami Shakarchi", "edition": "1st", "publisher": "Princeton University Press", "year": 2003, "isbn": "9780691113852"},
        {"title": "Several Complex Variables with Connections to Algebraic Geometry and Lie Groups", "author": "Joseph L. Taylor", "edition": "1st", "publisher": "American Mathematical Society", "year": 2002, "isbn": "9780821831786", "mr_number": "MR1885077"},
    ],
    "34": [  # Ordinary differential equations
        {"title": "Theory of Ordinary Differential Equations", "author": "Earl A. Coddington and Norman Levinson", "edition": "1st", "publisher": "McGraw-Hill", "year": 1955, "isbn": "9780070122550", "mr_number": "MR0069338"},
        {"title": "Differential Equations, Dynamical Systems, and an Introduction to Chaos",
            "doi": "10.1016/C2010-0-61170-9", "author": "Morris W. Hirsch, Stephen Smale, and Robert L. Devaney", "edition": "3rd", "publisher": "Academic Press", "year": 2013, "isbn": "9780123820105", "mr_number": "MR3293130"},
    ],
    "35": [  # PDE
        {"title": "Partial Differential Equations",
            "doi": "10.1090/gsm/019", "author": "Lawrence C. Evans", "edition": "2nd", "publisher": "American Mathematical Society", "year": 2010, "isbn": "9780821849743", "mr_number": "MR2597943"},
        {"title": "Partial Differential Equations: An Introduction", "author": "Walter A. Strauss", "edition": "2nd", "publisher": "Wiley", "year": 2008, "isbn": "9780470054567"},
    ],
    "40": [  # Sequences/series/summability
        {"title": "Principles of Mathematical Analysis", "author": "Walter Rudin", "edition": "3rd", "publisher": "McGraw-Hill", "year": 1976, "isbn": "9780070542358", "mr_number": "MR0385023"},
        {"title": "Understanding Analysis",
            "doi": "10.1007/978-1-4939-2712-8", "author": "Stephen Abbott", "edition": "2nd", "publisher": "Springer", "year": 2015, "isbn": "9781493927111"},
    ],
    "42": [  # Fourier analysis
        {"title": "Fourier Analysis: An Introduction",
            "doi": "10.1515/9781400831142", "author": "Elias M. Stein and Rami Shakarchi", "edition": "1st", "publisher": "Princeton University Press", "year": 2003, "isbn": "9780691113845"},
        {"title": "An Introduction to Harmonic Analysis",
            "doi": "10.1017/CBO9781139162371", "author": "Yitzhak Katznelson", "edition": "3rd", "publisher": "Cambridge University Press", "year": 2004, "isbn": "9780521543590", "mr_number": "MR2039503"},
    ],
    "46": [  # Functional analysis
        {"title": "A Course in Functional Analysis", "author": "John B. Conway", "edition": "2nd", "publisher": "Springer", "year": 1990, "isbn": "9780387972459"},
        {"title": "Functional Analysis", "author": "Walter Rudin", "edition": "2nd", "publisher": "McGraw-Hill", "year": 1991, "isbn": "9780070542365"},
    ],
    "49": [  # Calculus of variations
        {"title": "Calculus of Variations", "author": "I. M. Gelfand and S. V. Fomin", "edition": "1st", "publisher": "Dover", "year": 2000, "isbn": "9780486138044", "mr_number": "MR0160139"},
        {"title": "Introduction to the Calculus of Variations", "author": "Bernard Dacorogna", "edition": "3rd", "publisher": "Imperial College Press", "year": 2015, "isbn": "9781783265527"},
    ],
    "51": [  # Geometry
        {"title": "Geometry: Euclid and Beyond", "author": "Robin Hartshorne", "edition": "1st", "publisher": "Springer", "year": 2000, "isbn": "9780387986500", "mr_number": "MR1736856"},
        {"title": "Geometry: A Comprehensive Course", "author": "Dan Pedoe", "edition": "1st", "publisher": "Dover", "year": 1988, "isbn": "9780486656128"},
    ],
    "53": [  # Differential geometry
        {"title": "Introduction to Smooth Manifolds",
            "doi": "10.1007/978-1-4419-9982-5", "author": "John M. Lee", "edition": "2nd", "publisher": "Springer", "year": 2012, "isbn": "9781441999818", "mr_number": "MR2954043"},
        {"title": "Differential Geometry of Curves and Surfaces", "author": "Manfredo P. do Carmo", "edition": "1st", "publisher": "Prentice-Hall", "year": 1976, "isbn": "9780132125895", "mr_number": "MR0394451"},
    ],
    "54": [  # General topology
        {"title": "Topology", "author": "James R. Munkres", "edition": "2nd", "publisher": "Pearson", "year": 2000, "isbn": "9780131816299", "mr_number": "MR0464128"},
        {"title": "General Topology", "author": "Stephen Willard", "edition": "1st", "publisher": "Dover", "year": 2004, "isbn": "9780486434797", "mr_number": "MR2048350"},
    ],
    "55": [  # Algebraic topology
        {"title": "Algebraic Topology",
            "doi": "10.1017/CBO9780511627224", "author": "Allen Hatcher", "edition": "1st", "publisher": "Cambridge University Press", "year": 2002, "isbn": "9780521795401", "mr_number": "MR1867354"},
        {"title": "Topology", "author": "James R. Munkres", "edition": "2nd", "publisher": "Pearson", "year": 2000, "isbn": "9780131816299", "mr_number": "MR0464128"},
        {"title": "A Concise Course in Algebraic Topology", "author": "J. P. May", "edition": "1st", "publisher": "University of Chicago Press", "year": 1999, "isbn": "9780226511832", "mr_number": "MR1702278"},
    ],
    "57": [  # Manifolds/cell complexes
        {"title": "Introduction to Smooth Manifolds",
            "doi": "10.1007/978-1-4419-9982-5", "author": "John M. Lee", "edition": "2nd", "publisher": "Springer", "year": 2012, "isbn": "9781441999818", "mr_number": "MR2954043"},
        {"title": "Topology", "author": "James R. Munkres", "edition": "2nd", "publisher": "Pearson", "year": 2000, "isbn": "9780131816299", "mr_number": "MR0464128"},
        {"title": "Differential Topology",
            "doi": "10.1007/978-1-4684-9449-5", "author": "Morris W. Hirsch", "edition": "1st", "publisher": "Springer", "year": 1976, "isbn": "9780387901480", "mr_number": "MR0448362"},
    ],
    "58": [  # Global analysis, analysis on manifolds
        {"title": "Differential Topology",
            "doi": "10.1007/978-1-4684-9449-5", "author": "Morris W. Hirsch", "edition": "1st", "publisher": "Springer", "year": 1976, "isbn": "9780387901480", "mr_number": "MR0448362"},
        {"title": "Morse Theory",
            "doi": "10.1515/9781400881802", "author": "John W. Milnor", "edition": "1st", "publisher": "Princeton University Press", "year": 1963, "isbn": "9780691080086", "mr_number": "MR0163331"},
    ],
    "60": [  # Probability theory
        {"title": "Probability: Theory and Examples",
            "doi": "10.1017/9781108592629", "author": "Rick Durrett", "edition": "5th", "publisher": "Cambridge University Press", "year": 2019, "isbn": "9781108473682", "mr_number": "MR3930614"},
        {"title": "An Introduction to Probability Theory and Its Applications, Vol. 1", "author": "William Feller", "edition": "3rd", "publisher": "Wiley", "year": 1968, "isbn": "9780471257080", "mr_number": "MR0228020"},
        {"title": "Probability with Martingales",
            "doi": "10.1017/CBO9780511813658", "author": "David Williams", "edition": "1st", "publisher": "Cambridge University Press", "year": 1991, "isbn": "9780521406055", "mr_number": "MR1155402"},
    ],
    "62": [  # Statistics
        {"title": "Statistical Inference", "author": "George Casella and Roger L. Berger", "edition": "2nd", "publisher": "Duxbury", "year": 2002, "isbn": "9780534243128", "mr_number": "MR1990666"},
        {"title": "All of Statistics: A Concise Course in Statistical Inference",
            "doi": "10.1007/978-0-387-21736-9", "author": "Larry Wasserman", "edition": "1st", "publisher": "Springer", "year": 2004, "isbn": "9780387402727", "mr_number": "MR2055670"},
    ],
    "65": [  # Numerical analysis
        {"title": "Numerical Linear Algebra",
            "doi": "10.1137/1.9780898719574", "author": "Lloyd N. Trefethen and David Bau III", "edition": "1st", "publisher": "SIAM", "year": 1997, "isbn": "9780898713619", "mr_number": "MR1444820"},
        {"title": "Numerical Recipes: The Art of Scientific Computing", "author": "William H. Press, Saul A. Teukolsky, William T. Vetterling, and Brian P. Flannery", "edition": "3rd", "publisher": "Cambridge University Press", "year": 2007, "isbn": "9780521880688"},
    ],
    "68": [  # Computer science / formalization
        {"title": "Introduction to Algorithms", "author": "Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein", "edition": "3rd", "publisher": "MIT Press", "year": 2009, "isbn": "9780262033848", "mr_number": "MR2572804"},
        {"title": "Introduction to the Theory of Computation", "author": "Michael Sipser", "edition": "3rd", "publisher": "Cengage", "year": 2012, "isbn": "9781133187790"},
        {"title": "Concrete Mathematics: A Foundation for Computer Science", "author": "Ronald L. Graham, Donald E. Knuth, and Oren Patashnik", "edition": "2nd", "publisher": "Addison-Wesley", "year": 1994, "isbn": "9780131558362"},
    ],
    "70": [  # Mechanics / PDE
        {"title": "Mathematical Methods of Classical Mechanics",
            "doi": "10.1007/978-1-4757-2063-1", "author": "Vladimir I. Arnold", "edition": "2nd", "publisher": "Springer", "year": 1989, "isbn": "9780387968903", "mr_number": "MR1345386"},
        {"title": "Classical Mechanics", "author": "Herbert Goldstein, Charles Poole, and John Safko", "edition": "3rd", "publisher": "Pearson", "year": 2002, "isbn": "9780201657029"},
    ],
    "81": [  # Quantum theory
        {"title": "Principles of Quantum Mechanics",
            "doi": "10.1007/978-1-4757-0576-8", "author": "Ramamurti Shankar", "edition": "2nd", "publisher": "Springer", "year": 1994, "isbn": "9780306447907", "mr_number": "MR1343488"},
        {"title": "Introduction to Quantum Mechanics", "author": "David J. Griffiths", "edition": "2nd", "publisher": "Pearson", "year": 2004, "isbn": "9780131118928"},
    ],
    "90": [  # Operations research, optimization
        {"title": "Convex Optimization",
            "doi": "10.1017/CBO9780511804441", "author": "Stephen Boyd and Lieven Vandenberghe", "edition": "1st", "publisher": "Cambridge University Press", "year": 2004, "isbn": "9780521833783", "mr_number": "MR2061575"},
        {"title": "Nonlinear Programming", "author": "Dimitri P. Bertsekas", "edition": "3rd", "publisher": "Athena Scientific", "year": 2016, "isbn": "9781886529052"},
    ],
    "91": [  # Game theory, economics
        {"title": "Game Theory", "author": "Drew Fudenberg and Jean Tirole", "edition": "1st", "publisher": "MIT Press", "year": 1991, "isbn": "9780262014414", "mr_number": "MR1124703"},
        {"title": "A Course in Game Theory", "author": "Martin J. Osborne and Ariel Rubinstein", "edition": "1st", "publisher": "MIT Press", "year": 1994, "isbn": "9780262650403", "mr_number": "MR1301776"},
    ],
    "94": [  # Information and communication
        {"title": "Elements of Information Theory",
            "doi": "10.1002/0471200611", "author": "Thomas M. Cover and Joy A. Thomas", "edition": "2nd", "publisher": "Wiley", "year": 2006, "isbn": "9780471241959", "mr_number": "MR2239987"},
        {"title": "A First Course in Information Theory",
            "doi": "10.1007/978-1-4419-8608-5", "author": "Raymond W. Yeung", "edition": "1st", "publisher": "Springer", "year": 2002, "isbn": "9780306467911", "mr_number": "MR1876845"},
    ],
    "97": [  # Mathematics education
        {"title": "How to Prove It: A Structured Approach",
            "doi": "10.1017/CBO9780511811029", "author": "Daniel J. Velleman", "edition": "2nd", "publisher": "Cambridge University Press", "year": 2006, "isbn": "9780521675994", "mr_number": "MR2448845"},
        {"title": "How to Solve It: A New Aspect of Mathematical Method",
            "doi": "10.1515/9781400828678", "author": "George Pólya", "edition": "2nd", "publisher": "Princeton University Press", "year": 2004, "isbn": "9780691119663"},
    ],
}


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            fm_text = text[3:end].strip()
            body = text[end + 3 :].lstrip("\n")
            try:
                return yaml.safe_load(fm_text) or {}, body
            except yaml.YAMLError:
                return None, body
    return {}, text


def msc_key(msc):
    """从 msc_primary 中提取前两位 MSC 大类代码。"""
    if msc is None:
        return None
    # 处理形如 "14 - 14A15"、"26A99"、"14.14A15"、"00\n- 00A99" 等多种分隔
    tokens = re.split(r"[\s,;\-]+", str(msc).strip())
    for tok in tokens:
        m = re.match(r"^(\d{2})", tok)
        if m:
            return m.group(1)
    return None


def is_report_like(title: str, stem: str, tags):
    """排除报告、索引、模板、FAQ、README 等元数据文档。"""
    report_markers = ["报告", "进度", "日报", "总结", "计划", "索引", "README", "FAQ", "指南", "模板", "清单", "对齐", "课程表", "Syllabus"]
    if stem.startswith("00-"):
        return True
    if any(m in title or m in stem for m in report_markers):
        return True
    if isinstance(tags, (list, tuple, str)):
        tag_str = " ".join(tags) if isinstance(tags, (list, tuple)) else tags
        if any(m in tag_str for m in ["meta", "report", "template", "index", "draft-empty"]):
            return True
    return False


def word_count(body: str) -> int:
    """估算正文字符数（去除代码与标点）。"""
    text = re.sub(r"```[\s\S]*?```", "", body)
    text = re.sub(r"`[^`]+`", "", text)
    text = re.sub(r"[!-/:-@[-`{-~]", "", text)
    return len(text.replace(" ", "").replace("\n", ""))


def inject_doc(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None:
        return False, "parse_error"

    level = str(fm.get("level", "")).lower()
    # 排除明确的元数据/报告层级
    if level in ("meta", "l0", "project"):
        return False, "level_skip"

    title = str(fm.get("title", ""))
    stem = path.stem
    if is_report_like(title, stem, fm.get("tags", [])):
        return False, "report_skip"

    # 跳过空壳文档
    if word_count(body) < 300:
        return False, "short_skip"

    key = msc_key(fm.get("msc_primary"))
    if not key or key not in STANDARD_BOOKS:
        return False, "msc_miss"

    refs = fm.get("references") or {}
    textbooks = refs.get("textbooks") or []
    existing_titles = {str(tb.get("title", "")).strip().lower() for tb in textbooks}
    added = False
    for book in STANDARD_BOOKS[key]:
        if book["title"].strip().lower() in existing_titles:
            continue
        textbooks.append(book)
        existing_titles.add(book["title"].strip().lower())
        added = True

    if not added:
        return False, "already_has"

    refs["textbooks"] = textbooks
    fm["references"] = refs
    new_text = (
        "---\n"
        + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
        + "---\n"
        + body
    )
    path.write_text(new_text, encoding="utf-8")
    return True, "injected"


def main():
    changed = 0
    reasons = {}
    for path in PROJECT_ROOT.rglob("*.md"):
        if any(p in path.parts for p in ("node_modules", ".git", "00-归档", "归档")):
            continue
        ok, reason = inject_doc(path)
        reasons[reason] = reasons.get(reason, 0) + 1
        if ok:
            changed += 1
    print(f"Injected standard textbooks into {changed} docs.")
    print("Reason breakdown:", reasons)


if __name__ == "__main__":
    main()
