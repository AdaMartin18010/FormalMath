#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为核心数学概念/定理文档注入具有 DOI / arXiv ID 的经典论文/原始文献。

用法：
    python scripts/inject_landmark_papers.py
"""

import yaml
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

# term -> list of paper dicts
LANDMARK_PAPERS = {
    "费马大定理": [
        {
            "title": "Modular elliptic curves and Fermat's Last Theorem",
            "author": "Andrew Wiles",
            "journal": "Annals of Mathematics",
            "year": 1995,
            "doi": "10.2307/2118559",
        },
        {
            "title": "Ring-theoretic properties of certain Hecke algebras",
            "author": "Richard Taylor, Andrew Wiles",
            "journal": "Annals of Mathematics",
            "year": 1995,
            "doi": "10.2307/2118560",
        },
    ],
    "庞加莱猜想": [
        {
            "title": "The entropy formula for the Ricci flow and its geometric applications",
            "author": "Grigori Perelman",
            "journal": "arXiv preprint",
            "year": 2002,
            "arxiv_id": "math/0211159",
        },
        {
            "title": "Ricci flow with surgery on three-manifolds",
            "author": "Grigori Perelman",
            "journal": "arXiv preprint",
            "year": 2003,
            "arxiv_id": "math/0303109",
        },
        {
            "title": "Finite extinction time for the solutions to the Ricci flow on certain three-manifolds",
            "author": "Grigori Perelman",
            "journal": "arXiv preprint",
            "year": 2003,
            "arxiv_id": "math/0307245",
        },
    ],
    "孪生素数": [
        {
            "title": "Bounded gaps between primes",
            "author": "Yitang Zhang",
            "journal": "Annals of Mathematics",
            "year": 2014,
            "doi": "10.4007/annals.2014.179.3.7",
        },
    ],
    "素数间隙": [
        {
            "title": "Small gaps between primes",
            "author": "James Maynard",
            "journal": "Annals of Mathematics",
            "year": 2015,
            "doi": "10.4007/annals.2015.181.1.7",
        },
    ],
    "Green-Tao": [
        {
            "title": "The primes contain arbitrarily long arithmetic progressions",
            "author": "Ben Green, Terence Tao",
            "journal": "Annals of Mathematics",
            "year": 2008,
            "doi": "10.4007/annals.2008.167.481",
            "arxiv_id": "math/0404188",
        },
    ],
    "Weil猜想": [
        {
            "title": "La conjecture de Weil. I",
            "author": "Pierre Deligne",
            "journal": "Publications Mathématiques de l'IHÉS",
            "year": 1974,
            "doi": "10.1007/BF02684673",
        },
    ],
    "指标定理": [
        {
            "title": "The Index of Elliptic Operators on Compact Manifolds",
            "author": "Michael F. Atiyah, Isadore M. Singer",
            "journal": "Annals of Mathematics",
            "year": 1963,
            "doi": "10.2307/1970715",
        },
    ],
    "模型范畴": [
        {
            "title": "Homotopical Algebra",
            "author": "Daniel G. Quillen",
            "journal": "Lecture Notes in Mathematics",
            "year": 1967,
            "doi": "10.1007/BFb0097438",
        },
    ],
    "范畴论": [
        {
            "title": "General Theory of Natural Equivalences",
            "author": "Samuel Eilenberg, Saunders Mac Lane",
            "journal": "Transactions of the American Mathematical Society",
            "year": 1945,
            "doi": "10.2307/2269622",
        },
    ],
    "哥德尔不完备": [
        {
            "title": "Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I",
            "author": "Kurt Gödel",
            "journal": "Monatshefte für Mathematik und Physik",
            "year": 1931,
            "doi": "10.1007/BF01700692",
        },
    ],
    "图灵机": [
        {
            "title": "On Computable Numbers, with an Application to the Entscheidungsproblem",
            "author": "Alan M. Turing",
            "journal": "Proceedings of the London Mathematical Society",
            "year": 1937,
            "doi": "10.1112/plms/s2-42.1.230",
        },
    ],
    "黎曼猜想": [
        {
            "title": "Über die Anzahl der Primzahlen unter einer gegebenen Grösse",
            "author": "Bernhard Riemann",
            "journal": "Monatsberichte der Berliner Akademie",
            "year": 1859,
            "url": "https://www.claymath.org/publications/riemanns-1859-manuscript/",
        },
    ],
    "朗兰兹纲领": [
        {
            "title": "Problems in the Theory of Automorphic Forms",
            "author": "Robert P. Langlands",
            "journal": "Lecture Notes in Mathematics",
            "year": 1970,
            "doi": "10.1007/BFb0079065",
        },
    ],
    "黎曼-罗赫": [
        {
            "title": "Le théorème de Riemann-Roch",
            "author": "Armand Borel, Jean-Pierre Serre",
            "journal": "Bulletin de la Société Mathématique de France",
            "year": 1958,
            "doi": "10.24033/bsmf.1500",
        },
    ],
    "Riemann-Roch": [
        {
            "title": "Le théorème de Riemann-Roch",
            "author": "Armand Borel, Jean-Pierre Serre",
            "journal": "Bulletin de la Société Mathématique de France",
            "year": 1958,
            "doi": "10.24033/bsmf.1500",
        },
    ],
    "Serre对偶": [
        {
            "title": "Faisceaux algébriques cohérents",
            "author": "Jean-Pierre Serre",
            "journal": "Annals of Mathematics",
            "year": 1955,
            "doi": "10.2307/1970375",
        },
    ],
    "Bott周期性": [
        {
            "title": "The stable homotopy of the classical groups",
            "author": "Raoul Bott",
            "journal": "Annals of Mathematics",
            "year": 1959,
            "doi": "10.2307/1970106",
        },
    ],
    "法尔廷斯": [
        {
            "title": "Endlichkeitssätze für abelsche Varietäten über Zahlkörpern",
            "author": "Gerd Faltings",
            "journal": "Inventiones Mathematicae",
            "year": 1983,
            "doi": "10.1007/BF01388834",
        },
    ],
    "谷山-志村": [
        {
            "title": "On the modularity of elliptic curves over Q: wild 3-adic exercises",
            "author": "Christophe Breuil, Brian Conrad, Fred Diamond, Richard Taylor",
            "journal": "Journal of the American Mathematical Society",
            "year": 2001,
            "doi": "10.1090/S0894-0347-01-00370-8",
        },
    ],
    "P与NP": [
        {
            "title": "The complexity of theorem-proving procedures",
            "author": "Stephen A. Cook",
            "journal": "Proceedings of the Third Annual ACM Symposium on Theory of Computing",
            "year": 1971,
            "doi": "10.1145/800157.805047",
        },
    ],
    "连续统假设": [
        {
            "title": "The independence of the continuum hypothesis",
            "author": "Paul J. Cohen",
            "journal": "Proceedings of the National Academy of Sciences",
            "year": 1963,
            "doi": "10.1073/pnas.50.6.1143",
        },
    ],
    "RSA": [
        {
            "title": "A method for obtaining digital signatures and public-key cryptosystems",
            "author": "Ronald L. Rivest, Adi Shamir, Leonard M. Adleman",
            "journal": "Communications of the ACM",
            "year": 1978,
            "doi": "10.1145/359340.359342",
        },
    ],
    "香农": [
        {
            "title": "A mathematical theory of communication",
            "author": "Claude E. Shannon",
            "journal": "Bell System Technical Journal",
            "year": 1948,
            "url": "https://doi.org/10.1002/j.1538-7305.1948.tb01338.x",
        },
    ],
    "完美胚空间": [
        {
            "title": "Perfectoid spaces",
            "author": "Peter Scholze",
            "journal": "Publications Mathématiques de l'IHÉS",
            "year": 2012,
            "doi": "10.1007/s10240-012-0042-x",
        },
    ],
    "KPZ方程": [
        {
            "title": "Dynamic scaling of growing interfaces",
            "author": "Mehran Kardar, Giorgio Parisi, Yi-Cheng Zhang",
            "journal": "Physical Review Letters",
            "year": 1986,
            "doi": "10.1103/PhysRevLett.56.889",
        },
    ],
    "费特-汤普森": [
        {
            "title": "Solvability of groups of odd order",
            "author": "Walter Feit, John G. Thompson",
            "journal": "Pacific Journal of Mathematics",
            "year": 1963,
            "doi": "10.2140/pjm.1963.13.775",
        },
    ],
    "开普勒猜想": [
        {
            "title": "A proof of the Kepler conjecture",
            "author": "Thomas C. Hales",
            "journal": "Annals of Mathematics",
            "year": 2005,
            "doi": "10.4007/annals.2005.162.1065",
        },
    ],
    "莫尔斯理论": [
        {
            "title": "Relations between the critical points of a real function of n independent variables",
            "author": "Marston Morse",
            "journal": "Transactions of the American Mathematical Society",
            "year": 1925,
            "doi": "10.2307/1989176",
        },
    ],
    "布劳威尔不动点": [
        {
            "title": "Über Abbildung von Mannigfaltigkeiten",
            "author": "L. E. J. Brouwer",
            "journal": "Mathematische Annalen",
            "year": 1912,
            "doi": "10.1007/BF01444152",
        },
    ],
    "亚当斯谱序列": [
        {
            "title": "On the structure and applications of the Steenrod algebra",
            "author": "J. Frank Adams",
            "journal": "Commentarii Mathematici Helvetici",
            "year": 1958,
            "doi": "10.1007/BF02565974",
        },
    ],
    "布朗运动": [
        {
            "title": "Über die von der molekularkinetischen Energie der Wärme geforderte Bewegung von in ruhenden Flüssigkeiten suspendierten Teilchen",
            "author": "Albert Einstein",
            "journal": "Annalen der Physik",
            "year": 1905,
            "doi": "10.1002/andp.19053220806",
        },
    ],
    "高斯-博内": [
        {
            "title": "A simple intrinsic proof of the Gauss-Bonnet formula for closed Riemannian manifolds",
            "author": "Shiing-Shen Chern",
            "journal": "Annals of Mathematics",
            "year": 1944,
            "doi": "10.2307/1969302",
        },
    ],
    "陈类": [
        {
            "title": "Characteristic classes of Hermitian manifolds",
            "author": "Shiing-Shen Chern",
            "journal": "Annals of Mathematics",
            "year": 1946,
            "doi": "10.2307/1969037",
        },
    ],
    "Yang-Mills": [
        {
            "title": "Conservation of Isotopic Spin and Isotopic Gauge Invariance",
            "author": "C. N. Yang and R. L. Mills",
            "journal": "Physical Review",
            "year": 1954,
            "doi": "10.1103/PhysRev.96.191",
        },
    ],
    "纳什均衡": [
        {
            "title": "Equilibrium points in n-person games",
            "author": "John F. Nash",
            "journal": "Proceedings of the National Academy of Sciences",
            "year": 1950,
            "doi": "10.1073/pnas.36.1.48",
        },
    ],
    "博弈论": [
        {
            "title": "Zur Theorie der Gesellschaftsspiele",
            "author": "John von Neumann",
            "journal": "Mathematische Annalen",
            "year": 1928,
            "doi": "10.1007/BF01448847",
        },
    ],
    "Ramsey": [
        {
            "title": "On a problem of formal logic",
            "author": "F. P. Ramsey",
            "journal": "Proceedings of the London Mathematical Society",
            "year": 1930,
            "doi": "10.1112/plms/s2-30.1.264",
        },
    ],
    "中心极限定理": [
        {
            "title": "Eine neue Herleitung des Exponentialgesetzes in der Wahrscheinlichkeitsrechnung",
            "author": "Jarl Waldemar Lindeberg",
            "journal": "Mathematische Zeitschrift",
            "year": 1922,
            "doi": "10.1007/BF01494348",
        },
    ],
    "central limit theorem": [
        {
            "title": "Eine neue Herleitung des Exponentialgesetzes in der Wahrscheinlichkeitsrechnung",
            "author": "Jarl Waldemar Lindeberg",
            "journal": "Mathematische Zeitschrift",
            "year": 1922,
            "doi": "10.1007/BF01494348",
        },
    ],
    "蒙特卡洛": [
        {
            "title": "Equation of state calculations by fast computing machines",
            "author": "Nicholas Metropolis, Arianna W. Rosenbluth, Marshall N. Rosenbluth, Augusta H. Teller, and Edward Teller",
            "journal": "The Journal of Chemical Physics",
            "year": 1953,
            "doi": "10.1063/1.1699114",
        },
    ],
    "Monte Carlo": [
        {
            "title": "Equation of state calculations by fast computing machines",
            "author": "Nicholas Metropolis, Arianna W. Rosenbluth, Marshall N. Rosenbluth, Augusta H. Teller, and Edward Teller",
            "journal": "The Journal of Chemical Physics",
            "year": 1953,
            "doi": "10.1063/1.1699114",
        },
    ],
    "快速傅里叶变换": [
        {
            "title": "An algorithm for the machine calculation of complex Fourier series",
            "author": "James W. Cooley and John W. Tukey",
            "journal": "Mathematics of Computation",
            "year": 1965,
            "doi": "10.1090/S0025-5718-1965-0178586-1",
        },
    ],
    "FFT": [
        {
            "title": "An algorithm for the machine calculation of complex Fourier series",
            "author": "James W. Cooley and John W. Tukey",
            "journal": "Mathematics of Computation",
            "year": 1965,
            "doi": "10.1090/S0025-5718-1965-0178586-1",
        },
    ],
    "Hamming": [
        {
            "title": "Error detecting and error correcting codes",
            "author": "Richard W. Hamming",
            "journal": "Bell System Technical Journal",
            "year": 1950,
            "doi": "10.1002/j.1538-7305.1950.tb00463.x",
        },
    ],
    "编码理论": [
        {
            "title": "Error detecting and error correcting codes",
            "author": "Richard W. Hamming",
            "journal": "Bell System Technical Journal",
            "year": 1950,
            "doi": "10.1002/j.1538-7305.1950.tb00463.x",
        },
    ],
    "Diffie-Hellman": [
        {
            "title": "New directions in cryptography",
            "author": "Whitfield Diffie and Martin E. Hellman",
            "journal": "IEEE Transactions on Information Theory",
            "year": 1976,
            "doi": "10.1109/TIT.1976.1055638",
        },
    ],
    "公钥密码": [
        {
            "title": "New directions in cryptography",
            "author": "Whitfield Diffie and Martin E. Hellman",
            "journal": "IEEE Transactions on Information Theory",
            "year": 1976,
            "doi": "10.1109/TIT.1976.1055638",
        },
    ],
    "压缩感知": [
        {
            "title": "Robust uncertainty principles: exact signal reconstruction from highly incomplete frequency information",
            "author": "Emmanuel J. Candès, Justin Romberg, and Terence Tao",
            "journal": "Journal of the American Mathematical Society",
            "year": 2006,
            "doi": "10.1090/S0894-0347-06-00531-X",
            "arxiv_id": "math/0409186",
        },
    ],
    "compressed sensing": [
        {
            "title": "Robust uncertainty principles: exact signal reconstruction from highly incomplete frequency information",
            "author": "Emmanuel J. Candès, Justin Romberg, and Terence Tao",
            "journal": "Journal of the American Mathematical Society",
            "year": 2006,
            "doi": "10.1090/S0894-0347-06-00531-X",
            "arxiv_id": "math/0409186",
        },
    ],
    "深度学习": [
        {
            "title": "Deep learning",
            "author": "Yann LeCun, Yoshua Bengio, and Geoffrey Hinton",
            "journal": "Nature",
            "year": 2015,
            "doi": "10.1038/nature14539",
        },
    ],
    "deep learning": [
        {
            "title": "Deep learning",
            "author": "Yann LeCun, Yoshua Bengio, and Geoffrey Hinton",
            "journal": "Nature",
            "year": 2015,
            "doi": "10.1038/nature14539",
        },
    ],
    "Transformer": [
        {
            "title": "Attention is all you need",
            "author": "Ashish Vaswani, Noam Shazeer, Niki Parmar, Jakob Uszkoreit, Llion Jones, Aidan N. Gomez, Łukasz Kaiser, and Illia Polosukhin",
            "journal": "Advances in Neural Information Processing Systems",
            "year": 2017,
            "arxiv_id": "1706.03762",
        },
    ],
    "注意力机制": [
        {
            "title": "Attention is all you need",
            "author": "Ashish Vaswani, Noam Shazeer, Niki Parmar, Jakob Uszkoreit, Llion Jones, Aidan N. Gomez, Łukasz Kaiser, and Illia Polosukhin",
            "journal": "Advances in Neural Information Processing Systems",
            "year": 2017,
            "arxiv_id": "1706.03762",
        },
    ],
    "Hodge猜想": [
        {
            "title": "The topological invariants of algebraic varieties",
            "author": "W. V. D. Hodge",
            "journal": "Proceedings of the International Congress of Mathematicians",
            "year": 1950,
            "doi": "10.1142/9789814350364_0001",
        },
    ],
    "Hodge conjecture": [
        {
            "title": "The topological invariants of algebraic varieties",
            "author": "W. V. D. Hodge",
            "journal": "Proceedings of the International Congress of Mathematicians",
            "year": 1950,
            "doi": "10.1142/9789814350364_0001",
        },
    ],
    "Birch-Swinnerton-Dyer": [
        {
            "title": "Notes on elliptic curves. II",
            "author": "Bryan Birch and Peter Swinnerton-Dyer",
            "journal": "Journal für die reine und angewandte Mathematik",
            "year": 1965,
            "doi": "10.1515/crll.1965.218.79",
        },
    ],
    "BSD": [
        {
            "title": "Notes on elliptic curves. II",
            "author": "Bryan Birch and Peter Swinnerton-Dyer",
            "journal": "Journal für die reine und angewandte Mathematik",
            "year": 1965,
            "doi": "10.1515/crll.1965.218.79",
        },
    ],
    "配边": [
        {
            "title": "Quelques propriétés globales des variétés différentiables",
            "author": "René Thom",
            "journal": "Commentarii Mathematici Helvetici",
            "year": 1954,
            "doi": "10.1007/BF02566923",
        },
    ],
    "cobordism": [
        {
            "title": "Quelques propriétés globales des variétés différentiables",
            "author": "René Thom",
            "journal": "Commentarii Mathematici Helvetici",
            "year": 1954,
            "doi": "10.1007/BF02566923",
        },
    ],
    "小平消没": [
        {
            "title": "On a differential-geometric method in the theory of analytic stacks",
            "author": "Kunihiko Kodaira",
            "journal": "Proceedings of the National Academy of Sciences",
            "year": 1953,
            "doi": "10.1073/pnas.39.12.1268",
        },
    ],
    "Kodaira vanishing": [
        {
            "title": "On a differential-geometric method in the theory of analytic stacks",
            "author": "Kunihiko Kodaira",
            "journal": "Proceedings of the National Academy of Sciences",
            "year": 1953,
            "doi": "10.1073/pnas.39.12.1268",
        },
    ],
    "GAGA": [
        {
            "title": "Géométrie algébrique et géométrie analytique",
            "author": "Jean-Pierre Serre",
            "journal": "Annales de l'Institut Fourier",
            "year": 1956,
            "doi": "10.5802/aif.59",
        },
    ],
    "代数K理论": [
        {
            "title": "Higher algebraic K-theory. I",
            "author": "Daniel Quillen",
            "journal": "Lecture Notes in Mathematics",
            "year": 1973,
            "doi": "10.1007/BFb0067053",
        },
    ],
    "algebraic K-theory": [
        {
            "title": "Higher algebraic K-theory. I",
            "author": "Daniel Quillen",
            "journal": "Lecture Notes in Mathematics",
            "year": 1973,
            "doi": "10.1007/BFb0067053",
        },
    ],
    "同伦类型论": [
        {
            "title": "Homotopy theoretic models of identity types",
            "author": "Steve Awodey and Michael A. Warren",
            "journal": "Mathematical Proceedings of the Cambridge Philosophical Society",
            "year": 2008,
            "doi": "10.1017/S0305004107001823",
            "arxiv_id": "0709.3431",
        },
    ],
    "homotopy type theory": [
        {
            "title": "Homotopy theoretic models of identity types",
            "author": "Steve Awodey and Michael A. Warren",
            "journal": "Mathematical Proceedings of the Cambridge Philosophical Society",
            "year": 2008,
            "doi": "10.1017/S0305004107001823",
            "arxiv_id": "0709.3431",
        },
    ],
    "遍历理论": [
        {
            "title": "Proof of the ergodic theorem",
            "author": "George D. Birkhoff",
            "journal": "Proceedings of the National Academy of Sciences",
            "year": 1931,
            "doi": "10.1073/pnas.17.12.656",
        },
    ],
    "ergodic theory": [
        {
            "title": "Proof of the ergodic theorem",
            "author": "George D. Birkhoff",
            "journal": "Proceedings of the National Academy of Sciences",
            "year": 1931,
            "doi": "10.1073/pnas.17.12.656",
        },
    ],
    "随机矩阵": [
        {
            "title": "Characteristic vectors of bordered matrices with infinite dimensions",
            "author": "Eugene P. Wigner",
            "journal": "Annals of Mathematics",
            "year": 1955,
            "doi": "10.2307/1970079",
        },
    ],
    "random matrix": [
        {
            "title": "Characteristic vectors of bordered matrices with infinite dimensions",
            "author": "Eugene P. Wigner",
            "journal": "Annals of Mathematics",
            "year": 1955,
            "doi": "10.2307/1970079",
        },
    ],
    "渗流": [
        {
            "title": "Percolation processes. I. Crystals and mazes",
            "author": "Simon R. Broadbent and John M. Hammersley",
            "journal": "Mathematical Proceedings of the Cambridge Philosophical Society",
            "year": 1957,
            "doi": "10.1017/S0305004100032680",
        },
    ],
    "percolation": [
        {
            "title": "Percolation processes. I. Crystals and mazes",
            "author": "Simon R. Broadbent and John M. Hammersley",
            "journal": "Mathematical Proceedings of the Cambridge Philosophical Society",
            "year": 1957,
            "doi": "10.1017/S0305004100032680",
        },
    ],
    "纽结": [
        {
            "title": "A polynomial invariant for knots via von Neumann algebras",
            "author": "Vaughan F. R. Jones",
            "journal": "Bulletin of the American Mathematical Society",
            "year": 1985,
            "doi": "10.1090/S0273-0979-1985-15304-2",
        },
    ],
    "knot": [
        {
            "title": "A polynomial invariant for knots via von Neumann algebras",
            "author": "Vaughan F. R. Jones",
            "journal": "Bulletin of the American Mathematical Society",
            "year": 1985,
            "doi": "10.1090/S0273-0979-1985-15304-2",
        },
    ],
    "Jones多项式": [
        {
            "title": "A polynomial invariant for knots via von Neumann algebras",
            "author": "Vaughan F. R. Jones",
            "journal": "Bulletin of the American Mathematical Society",
            "year": 1985,
            "doi": "10.1090/S0273-0979-1985-15304-2",
        },
    ],
    "采样定理": [
        {
            "title": "Certain topics in telegraph transmission theory",
            "author": "Harry Nyquist",
            "journal": "Transactions of the American Institute of Electrical Engineers",
            "year": 1928,
            "doi": "10.1109/T-AIEE.1928.5055024",
        },
    ],
    "sampling theorem": [
        {
            "title": "Certain topics in telegraph transmission theory",
            "author": "Harry Nyquist",
            "journal": "Transactions of the American Institute of Electrical Engineers",
            "year": 1928,
            "doi": "10.1109/T-AIEE.1928.5055024",
        },
    ],
    "小波": [
        {
            "title": "Orthonormal bases of compactly supported wavelets",
            "author": "Ingrid Daubechies",
            "journal": "Communications on Pure and Applied Mathematics",
            "year": 1988,
            "doi": "10.1002/cpa.3160410705",
        },
    ],
    "wavelet": [
        {
            "title": "Orthonormal bases of compactly supported wavelets",
            "author": "Ingrid Daubechies",
            "journal": "Communications on Pure and Applied Mathematics",
            "year": 1988,
            "doi": "10.1002/cpa.3160410705",
        },
    ],
    "混沌": [
        {
            "title": "Deterministic nonperiodic flow",
            "author": "Edward N. Lorenz",
            "journal": "Journal of the Atmospheric Sciences",
            "year": 1963,
            "doi": "10.1175/1520-0469(1963)020<0130:DNF>2.0.CO;2",
        },
    ],
    "chaos": [
        {
            "title": "Deterministic nonperiodic flow",
            "author": "Edward N. Lorenz",
            "journal": "Journal of the Atmospheric Sciences",
            "year": 1963,
            "doi": "10.1175/1520-0469(1963)020<0130:DNF>2.0.CO;2",
        },
    ],
    "Lorenz": [
        {
            "title": "Deterministic nonperiodic flow",
            "author": "Edward N. Lorenz",
            "journal": "Journal of the Atmospheric Sciences",
            "year": 1963,
            "doi": "10.1175/1520-0469(1963)020<0130:DNF>2.0.CO;2",
        },
    ],
    "诺特定理": [
        {
            "title": "Invariante Variationsprobleme",
            "author": "Emmy Noether",
            "journal": "Nachrichten von der Gesellschaft der Wissenschaften zu Göttingen",
            "year": 1918,
            "doi": "10.1007/BF01466754",
        },
    ],
    "Noether theorem": [
        {
            "title": "Invariante Variationsprobleme",
            "author": "Emmy Noether",
            "journal": "Nachrichten von der Gesellschaft der Wissenschaften zu Göttingen",
            "year": 1918,
            "doi": "10.1007/BF01466754",
        },
    ],
    "选择公理": [
        {
            "title": "Beweis, daß jede Menge wohlgeordnet werden kann",
            "author": "Ernst Zermelo",
            "journal": "Mathematische Annalen",
            "year": 1904,
            "doi": "10.1007/BF01445300",
        },
    ],
    "axiom of choice": [
        {
            "title": "Beweis, daß jede Menge wohlgeordnet werden kann",
            "author": "Ernst Zermelo",
            "journal": "Mathematische Annalen",
            "year": 1904,
            "doi": "10.1007/BF01445300",
        },
    ],
    "佐恩引理": [
        {
            "title": "A remark on method in transfinite algebra",
            "author": "Max Zorn",
            "journal": "Bulletin of the American Mathematical Society",
            "year": 1935,
            "doi": "10.1090/S0002-9904-1935-06166-X",
        },
    ],
    "Zorn's lemma": [
        {
            "title": "A remark on method in transfinite algebra",
            "author": "Max Zorn",
            "journal": "Bulletin of the American Mathematical Society",
            "year": 1935,
            "doi": "10.1090/S0002-9904-1935-06166-X",
        },
    ],
    "集合论公理": [
        {
            "title": "Untersuchungen über die Grundlagen der Mengenlehre I",
            "author": "Ernst Zermelo",
            "journal": "Mathematische Annalen",
            "year": 1908,
            "doi": "10.1007/BF01449999",
        },
    ],
    "Zermelo-Fraenkel": [
        {
            "title": "Untersuchungen über die Grundlagen der Mengenlehre I",
            "author": "Ernst Zermelo",
            "journal": "Mathematische Annalen",
            "year": 1908,
            "doi": "10.1007/BF01449999",
        },
    ],
    "韦伊猜想": [
        {
            "title": "Numbers of solutions of equations in finite fields",
            "author": "André Weil",
            "journal": "Bulletin of the American Mathematical Society",
            "year": 1949,
            "doi": "10.1090/S0002-9904-1949-09219-4",
        },
    ],
    "Weil conjectures": [
        {
            "title": "Numbers of solutions of equations in finite fields",
            "author": "André Weil",
            "journal": "Bulletin of the American Mathematical Society",
            "year": 1949,
            "doi": "10.1090/S0002-9904-1949-09219-4",
        },
    ],
    "卡拉比-丘": [
        {
            "title": "On the Ricci curvature of a compact Kähler manifold and the complex Monge-Ampère equation. I",
            "author": "Shing-Tung Yau",
            "journal": "Communications on Pure and Applied Mathematics",
            "year": 1978,
            "doi": "10.1002/cpa.3160310304",
        },
    ],
    "Calabi-Yau": [
        {
            "title": "On the Ricci curvature of a compact Kähler manifold and the complex Monge-Ampère equation. I",
            "author": "Shing-Tung Yau",
            "journal": "Communications on Pure and Applied Mathematics",
            "year": 1978,
            "doi": "10.1002/cpa.3160310304",
        },
    ],
    "薛定谔方程": [
        {
            "title": "An undulatory theory of the mechanics of atoms and molecules",
            "author": "Erwin Schrödinger",
            "journal": "Physical Review",
            "year": 1926,
            "doi": "10.1103/PhysRev.28.1049",
        },
    ],
    "Schrödinger equation": [
        {
            "title": "An undulatory theory of the mechanics of atoms and molecules",
            "author": "Erwin Schrödinger",
            "journal": "Physical Review",
            "year": 1926,
            "doi": "10.1103/PhysRev.28.1049",
        },
    ],
    "海森堡": [
        {
            "title": "Über quantentheoretischer Umdeutung kinematischer und mechanischer Beziehungen",
            "author": "Werner Heisenberg",
            "journal": "Zeitschrift für Physik",
            "year": 1925,
            "doi": "10.1007/BF01328377",
        },
    ],
    "Heisenberg": [
        {
            "title": "Über quantentheoretischer Umdeutung kinematischer und mechanischer Beziehungen",
            "author": "Werner Heisenberg",
            "journal": "Zeitschrift für Physik",
            "year": 1925,
            "doi": "10.1007/BF01328377",
        },
    ],
    "狄拉克方程": [
        {
            "title": "The quantum theory of the electron",
            "author": "Paul A. M. Dirac",
            "journal": "Proceedings of the Royal Society A",
            "year": 1928,
            "doi": "10.1098/rspa.1928.0023",
        },
    ],
    "Dirac equation": [
        {
            "title": "The quantum theory of the electron",
            "author": "Paul A. M. Dirac",
            "journal": "Proceedings of the Royal Society A",
            "year": 1928,
            "doi": "10.1098/rspa.1928.0023",
        },
    ],
    "相对论": [
        {
            "title": "Zur Elektrodynamik bewegter Körper",
            "author": "Albert Einstein",
            "journal": "Annalen der Physik",
            "year": 1905,
            "doi": "10.1002/andp.19053221004",
        },
        {
            "title": "Die Grundlage der allgemeinen Relativitätstheorie",
            "author": "Albert Einstein",
            "journal": "Annalen der Physik",
            "year": 1916,
            "doi": "10.1002/andp.19163540702",
        },
    ],
    "relativity": [
        {
            "title": "Zur Elektrodynamik bewegter Körper",
            "author": "Albert Einstein",
            "journal": "Annalen der Physik",
            "year": 1905,
            "doi": "10.1002/andp.19053221004",
        },
        {
            "title": "Die Grundlage der allgemeinen Relativitätstheorie",
            "author": "Albert Einstein",
            "journal": "Annalen der Physik",
            "year": 1916,
            "doi": "10.1002/andp.19163540702",
        },
    ],
    "爱因斯坦": [
        {
            "title": "Zur Elektrodynamik bewegter Körper",
            "author": "Albert Einstein",
            "journal": "Annalen der Physik",
            "year": 1905,
            "doi": "10.1002/andp.19053221004",
        },
        {
            "title": "Über die von der molekularkinetischen Energie der Wärme geforderte Bewegung von in ruhenden Flüssigkeiten suspendierten Teilchen",
            "author": "Albert Einstein",
            "journal": "Annalen der Physik",
            "year": 1905,
            "doi": "10.1002/andp.19053220806",
        },
    ],
    "Einstein": [
        {
            "title": "Zur Elektrodynamik bewegter Körper",
            "author": "Albert Einstein",
            "journal": "Annalen der Physik",
            "year": 1905,
            "doi": "10.1002/andp.19053221004",
        },
    ],
    "标准模型": [
        {
            "title": "A model of leptons",
            "author": "Steven Weinberg",
            "journal": "Physical Review Letters",
            "year": 1967,
            "doi": "10.1103/PhysRevLett.19.1264",
        },
    ],
    "Standard Model": [
        {
            "title": "A model of leptons",
            "author": "Steven Weinberg",
            "journal": "Physical Review Letters",
            "year": 1967,
            "doi": "10.1103/PhysRevLett.19.1264",
        },
    ],
    "Higgs": [
        {
            "title": "Broken symmetries and the masses of gauge bosons",
            "author": "Peter W. Higgs",
            "journal": "Physical Review Letters",
            "year": 1964,
            "doi": "10.1103/PhysRevLett.13.508",
        },
    ],
    "希格斯": [
        {
            "title": "Broken symmetries and the masses of gauge bosons",
            "author": "Peter W. Higgs",
            "journal": "Physical Review Letters",
            "year": 1964,
            "doi": "10.1103/PhysRevLett.13.508",
        },
    ],
    "黑洞": [
        {
            "title": "Gravitational collapse and space-time singularities",
            "author": "Roger Penrose",
            "journal": "Physical Review Letters",
            "year": 1965,
            "doi": "10.1103/PhysRevLett.14.57",
        },
    ],
    "black hole": [
        {
            "title": "Gravitational collapse and space-time singularities",
            "author": "Roger Penrose",
            "journal": "Physical Review Letters",
            "year": 1965,
            "doi": "10.1103/PhysRevLett.14.57",
        },
    ],
    "引力波": [
        {
            "title": "Observation of gravitational waves from a binary black hole merger",
            "author": "B. P. Abbott et al. (LIGO Scientific Collaboration and Virgo Collaboration)",
            "journal": "Physical Review Letters",
            "year": 2016,
            "doi": "10.1103/PhysRevLett.116.061102",
        },
    ],
    "gravitational wave": [
        {
            "title": "Observation of gravitational waves from a binary black hole merger",
            "author": "B. P. Abbott et al. (LIGO Scientific Collaboration and Virgo Collaboration)",
            "journal": "Physical Review Letters",
            "year": 2016,
            "doi": "10.1103/PhysRevLett.116.061102",
        },
    ],
    "全息原理": [
        {
            "title": "The large N limit of superconformal field theories and supergravity",
            "author": "Juan Maldacena",
            "journal": "Advances in Theoretical and Mathematical Physics",
            "year": 1998,
            "doi": "10.4310/ATMP.1998.v2.n2.a1",
            "arxiv_id": "hep-th/9711200",
        },
    ],
    "holographic principle": [
        {
            "title": "The large N limit of superconformal field theories and supergravity",
            "author": "Juan Maldacena",
            "journal": "Advances in Theoretical and Mathematical Physics",
            "year": 1998,
            "doi": "10.4310/ATMP.1998.v2.n2.a1",
            "arxiv_id": "hep-th/9711200",
        },
    ],
    "AdS/CFT": [
        {
            "title": "The large N limit of superconformal field theories and supergravity",
            "author": "Juan Maldacena",
            "journal": "Advances in Theoretical and Mathematical Physics",
            "year": 1998,
            "doi": "10.4310/ATMP.1998.v2.n2.a1",
            "arxiv_id": "hep-th/9711200",
        },
    ],
    "超对称": [
        {
            "title": "Supergauge transformations in four dimensions",
            "author": "Julius Wess and Bruno Zumino",
            "journal": "Nuclear Physics B",
            "year": 1974,
            "doi": "10.1016/0550-3213(74)90555-2",
        },
    ],
    "supersymmetry": [
        {
            "title": "Supergauge transformations in four dimensions",
            "author": "Julius Wess and Bruno Zumino",
            "journal": "Nuclear Physics B",
            "year": 1974,
            "doi": "10.1016/0550-3213(74)90555-2",
        },
    ],
    "量子计算": [
        {
            "title": "Simulating physics with computers",
            "author": "Richard P. Feynman",
            "journal": "International Journal of Theoretical Physics",
            "year": 1982,
            "doi": "10.1007/BF02650179",
        },
    ],
    "quantum computing": [
        {
            "title": "Simulating physics with computers",
            "author": "Richard P. Feynman",
            "journal": "International Journal of Theoretical Physics",
            "year": 1982,
            "doi": "10.1007/BF02650179",
        },
    ],
    "量子纠错": [
        {
            "title": "Scheme for reducing decoherence in quantum computer memory",
            "author": "Peter W. Shor",
            "journal": "Physical Review A",
            "year": 1995,
            "doi": "10.1103/PhysRevA.52.R2493",
        },
    ],
    "quantum error correction": [
        {
            "title": "Scheme for reducing decoherence in quantum computer memory",
            "author": "Peter W. Shor",
            "journal": "Physical Review A",
            "year": 1995,
            "doi": "10.1103/PhysRevA.52.R2493",
        },
    ],
    "黑洞信息": [
        {
            "title": "Particle creation by black holes",
            "author": "Stephen W. Hawking",
            "journal": "Communications in Mathematical Physics",
            "year": 1975,
            "doi": "10.1007/BF02345020",
        },
    ],
    "Hawking radiation": [
        {
            "title": "Particle creation by black holes",
            "author": "Stephen W. Hawking",
            "journal": "Communications in Mathematical Physics",
            "year": 1975,
            "doi": "10.1007/BF02345020",
        },
    ],
    "Donaldson": [
        {
            "title": "An application of gauge theory to four-dimensional topology",
            "author": "Simon K. Donaldson",
            "journal": "Journal of Differential Geometry",
            "year": 1983,
            "doi": "10.4310/jdg/1214437665",
        },
    ],
    "唐纳森": [
        {
            "title": "An application of gauge theory to four-dimensional topology",
            "author": "Simon K. Donaldson",
            "journal": "Journal of Differential Geometry",
            "year": 1983,
            "doi": "10.4310/jdg/1214437665",
        },
    ],
    "四维流形": [
        {
            "title": "An application of gauge theory to four-dimensional topology",
            "author": "Simon K. Donaldson",
            "journal": "Journal of Differential Geometry",
            "year": 1983,
            "doi": "10.4310/jdg/1214437665",
        },
    ],
    "4-manifold": [
        {
            "title": "An application of gauge theory to four-dimensional topology",
            "author": "Simon K. Donaldson",
            "journal": "Journal of Differential Geometry",
            "year": 1983,
            "doi": "10.4310/jdg/1214437665",
        },
    ],
    "Seiberg-Witten": [
        {
            "title": "Monopoles and four-manifolds",
            "author": "Edward Witten",
            "journal": "Mathematical Research Letters",
            "year": 1994,
            "doi": "10.4310/MRL.1994.v1.n6.a13",
            "arxiv_id": "hep-th/9411102",
        },
    ],
    "塞伯格-威滕": [
        {
            "title": "Monopoles and four-manifolds",
            "author": "Edward Witten",
            "journal": "Mathematical Research Letters",
            "year": 1994,
            "doi": "10.4310/MRL.1994.v1.n6.a13",
            "arxiv_id": "hep-th/9411102",
        },
    ],
    "Floer": [
        {
            "title": "An instanton-invariant for 3-manifolds",
            "author": "Andreas Floer",
            "journal": "Communications in Mathematical Physics",
            "year": 1988,
            "doi": "10.1007/BF01223490",
        },
    ],
    "弗洛尔": [
        {
            "title": "An instanton-invariant for 3-manifolds",
            "author": "Andreas Floer",
            "journal": "Communications in Mathematical Physics",
            "year": 1988,
            "doi": "10.1007/BF01223490",
        },
    ],
    "Gromov": [
        {
            "title": "Pseudo holomorphic curves in symplectic manifolds",
            "author": "Mikhail Gromov",
            "journal": "Inventiones Mathematicae",
            "year": 1985,
            "doi": "10.1007/BF01388788",
        },
    ],
    "格罗莫夫": [
        {
            "title": "Pseudo holomorphic curves in symplectic manifolds",
            "author": "Mikhail Gromov",
            "journal": "Inventiones Mathematicae",
            "year": 1985,
            "doi": "10.1007/BF01388788",
        },
    ],
    "伪全纯曲线": [
        {
            "title": "Pseudo holomorphic curves in symplectic manifolds",
            "author": "Mikhail Gromov",
            "journal": "Inventiones Mathematicae",
            "year": 1985,
            "doi": "10.1007/BF01388788",
        },
    ],
    "Deligne-Mumford": [
        {
            "title": "The irreducibility of the space of curves of given genus",
            "author": "Pierre Deligne and David Mumford",
            "journal": "Publications Mathématiques de l'IHÉS",
            "year": 1969,
            "doi": "10.1007/BF02684599",
        },
    ],
    "稳定曲线": [
        {
            "title": "The irreducibility of the space of curves of given genus",
            "author": "Pierre Deligne and David Mumford",
            "journal": "Publications Mathématiques de l'IHÉS",
            "year": 1969,
            "doi": "10.1007/BF02684599",
        },
    ],
    "相交上同调": [
        {
            "title": "Intersection homology theory",
            "author": "Mark Goresky and Robert MacPherson",
            "journal": "Topology",
            "year": 1980,
            "doi": "10.1016/0040-9383(80)90003-8",
        },
    ],
    "intersection cohomology": [
        {
            "title": "Intersection homology theory",
            "author": "Mark Goresky and Robert MacPherson",
            "journal": "Topology",
            "year": 1980,
            "doi": "10.1016/0040-9383(80)90003-8",
        },
    ],
    "Goresky-MacPherson": [
        {
            "title": "Intersection homology theory",
            "author": "Mark Goresky and Robert MacPherson",
            "journal": "Topology",
            "year": 1980,
            "doi": "10.1016/0040-9383(80)90003-8",
        },
    ],
    "陈-韦伊": [
        {
            "title": "Hermitian vector bundles and the equidistribution of the zeroes of their holomorphic sections",
            "author": "Shiing-Shen Chern",
            "journal": "Acta Mathematica",
            "year": 1965,
            "doi": "10.1007/BF02392806",
        },
    ],
    "Chern-Weil": [
        {
            "title": "Hermitian vector bundles and the equidistribution of the zeroes of their holomorphic sections",
            "author": "Shiing-Shen Chern",
            "journal": "Acta Mathematica",
            "year": 1965,
            "doi": "10.1007/BF02392806",
        },
    ],
    "指标定理": [
        {
            "title": "The index of elliptic operators: III",
            "author": "Michael F. Atiyah and Isadore M. Singer",
            "journal": "Annals of Mathematics",
            "year": 1968,
            "doi": "10.2307/1970717",
        },
    ],
    "Atiyah-Singer": [
        {
            "title": "The index of elliptic operators: III",
            "author": "Michael F. Atiyah and Isadore M. Singer",
            "journal": "Annals of Mathematics",
            "year": 1968,
            "doi": "10.2307/1970717",
        },
    ],
    "霍普夫不变量": [
        {
            "title": "Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche",
            "author": "Heinz Hopf",
            "journal": "Mathematische Annalen",
            "year": 1931,
            "doi": "10.1007/BF01447805",
        },
    ],
    "Hopf invariant": [
        {
            "title": "Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche",
            "author": "Heinz Hopf",
            "journal": "Mathematische Annalen",
            "year": 1931,
            "doi": "10.1007/BF01447805",
        },
    ],
    "霍普夫纤维化": [
        {
            "title": "Über die Abbildungen von Sphären auf Sphären niedrigerer Dimension",
            "author": "Heinz Hopf",
            "journal": "Fundamenta Mathematicae",
            "year": 1935,
            "doi": "10.4064/fm-25-1-427-440",
        },
    ],
    "Hopf fibration": [
        {
            "title": "Über die Abbildungen von Sphären auf Sphären niedrigerer Dimension",
            "author": "Heinz Hopf",
            "journal": "Fundamenta Mathematicae",
            "year": 1935,
            "doi": "10.4064/fm-25-1-427-440",
        },
    ],
    "米尔诺怪球": [
        {
            "title": "On manifolds homeomorphic to the 7-sphere",
            "author": "John W. Milnor",
            "journal": "Annals of Mathematics",
            "year": 1956,
            "doi": "10.2307/1969983",
        },
    ],
    "exotic sphere": [
        {
            "title": "On manifolds homeomorphic to the 7-sphere",
            "author": "John W. Milnor",
            "journal": "Annals of Mathematics",
            "year": 1956,
            "doi": "10.2307/1969983",
        },
    ],
    "h-cobordism": [
        {
            "title": "On the structure of manifolds",
            "author": "Stephen Smale",
            "journal": "American Journal of Mathematics",
            "year": 1962,
            "doi": "10.2307/2372978",
        },
    ],
    "庞加莱猜想": [
        {
            "title": "The entropy formula for the Ricci flow and its geometric applications",
            "author": "Grigori Perelman",
            "journal": "arXiv preprint",
            "year": 2002,
            "arxiv_id": "math/0211159",
        },
        {
            "title": "Ricci flow with surgery on three-manifolds",
            "author": "Grigori Perelman",
            "journal": "arXiv preprint",
            "year": 2003,
            "arxiv_id": "math/0303109",
        },
    ],
    "Thurston": [
        {
            "title": "Three-dimensional manifolds, Kleinian groups and hyperbolic geometry",
            "author": "William P. Thurston",
            "journal": "Bulletin of the American Mathematical Society",
            "year": 1982,
            "doi": "10.1090/S0273-0979-1982-14503-4",
        },
    ],
    "瑟斯顿": [
        {
            "title": "Three-dimensional manifolds, Kleinian groups and hyperbolic geometry",
            "author": "William P. Thurston",
            "journal": "Bulletin of the American Mathematical Society",
            "year": 1982,
            "doi": "10.1090/S0273-0979-1982-14503-4",
        },
    ],
    "几何化猜想": [
        {
            "title": "Three-dimensional manifolds, Kleinian groups and hyperbolic geometry",
            "author": "William P. Thurston",
            "journal": "Bulletin of the American Mathematical Society",
            "year": 1982,
            "doi": "10.1090/S0273-0979-1982-14503-4",
        },
    ],
    "双曲几何": [
        {
            "title": "Three-dimensional manifolds, Kleinian groups and hyperbolic geometry",
            "author": "William P. Thurston",
            "journal": "Bulletin of the American Mathematical Society",
            "year": 1982,
            "doi": "10.1090/S0273-0979-1982-14503-4",
        },
    ],
    "KAM": [
        {
            "title": "On conservation of conditionally periodic motions for a small change in Hamilton's function",
            "author": "Andrey N. Kolmogorov",
            "journal": "Doklady Akademii Nauk SSSR",
            "year": 1954,
        },
    ],
    "柯尔莫哥洛夫": [
        {
            "title": "On conservation of conditionally periodic motions for a small change in Hamilton's function",
            "author": "Andrey N. Kolmogorov",
            "journal": "Doklady Akademii Nauk SSSR",
            "year": 1954,
        },
    ],
    "中心极限定理": [
        {
            "title": "Eine neue Herleitung des Exponentialgesetzes in der Wahrscheinlichkeitsrechnung",
            "author": "Jarl Waldemar Lindeberg",
            "journal": "Mathematische Zeitschrift",
            "year": 1922,
            "doi": "10.1007/BF01494348",
        },
    ],
    "概率论": [
        {
            "title": "Grundbegriffe der Wahrscheinlichkeitsrechnung",
            "author": "Andrey N. Kolmogorov",
            "journal": "Springer",
            "year": 1933,
        },
    ],
    "Kolmogorov": [
        {
            "title": "Grundbegriffe der Wahrscheinlichkeitsrechnung",
            "author": "Andrey N. Kolmogorov",
            "journal": "Springer",
            "year": 1933,
        },
    ],
    "蒙特卡洛": [
        {
            "title": "Equation of state calculations by fast computing machines",
            "author": "Nicholas Metropolis, Arianna W. Rosenbluth, Marshall N. Rosenbluth, Augusta H. Teller, and Edward Teller",
            "journal": "The Journal of Chemical Physics",
            "year": 1953,
            "doi": "10.1063/1.1699114",
        },
    ],
    "Monte Carlo": [
        {
            "title": "Equation of state calculations by fast computing machines",
            "author": "Nicholas Metropolis, Arianna W. Rosenbluth, Marshall N. Rosenbluth, Augusta H. Teller, and Edward Teller",
            "journal": "The Journal of Chemical Physics",
            "year": 1953,
            "doi": "10.1063/1.1699114",
        },
    ],
    "马尔可夫链": [
        {
            "title": "Rasprostranenie zakona bol'shih chisel na velichiny, zavisyaschie drug ot druga",
            "author": "Andrey A. Markov",
            "journal": "Izvestiya Fiziko-matematicheskogo obschestva pri Kazanskom universitete",
            "year": 1906,
        },
    ],
    "Markov chain": [
        {
            "title": "Rasprostranenie zakona bol'shih chisel na velichiny, zavisyaschie drug ot druga",
            "author": "Andrey A. Markov",
            "journal": "Izvestiya Fiziko-matematicheskogo obschestva pri Kazanskom universitete",
            "year": 1906,
        },
    ],
    "鞅": [
        {
            "title": "Stochastic Processes",
            "author": "Joseph L. Doob",
            "journal": "Wiley",
            "year": 1953,
        },
    ],
    "martingale": [
        {
            "title": "Stochastic Processes",
            "author": "Joseph L. Doob",
            "journal": "Wiley",
            "year": 1953,
        },
    ],
    "图论": [
        {
            "title": "Solutio problematis ad geometriam situs pertinentis",
            "author": "Leonhard Euler",
            "journal": "Commentarii Academiae Scientiarum Imperialis Petropolitanae",
            "year": 1736,
        },
    ],
    "graph theory": [
        {
            "title": "Solutio problematis ad geometriam situs pertinentis",
            "author": "Leonhard Euler",
            "journal": "Commentarii Academiae Scientiarum Imperialis Petropolitanae",
            "year": 1736,
        },
    ],
    "四色定理": [
        {
            "title": "Every planar map is four colorable",
            "author": "Kenneth Appel and Wolfgang Haken",
            "journal": "Illinois Journal of Mathematics",
            "year": 1977,
            "doi": "10.1215/ijm/1256049011",
        },
    ],
    "four color theorem": [
        {
            "title": "Every planar map is four colorable",
            "author": "Kenneth Appel and Wolfgang Haken",
            "journal": "Illinois Journal of Mathematics",
            "year": 1977,
            "doi": "10.1215/ijm/1256049011",
        },
    ],
}


def is_report_like(title: str, stem: str):
    report_markers = ["报告", "进度", "日报", "总结", "计划", "索引", "README", "FAQ", "指南", "模板", "清单"]
    if stem.startswith("00-"):
        return True
    if any(m in title or m in stem for m in report_markers):
        return True
    return False


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            fm_text = text[3:end].strip()
            body = text[end + 3 :].strip()
            try:
                return yaml.safe_load(fm_text) or {}, body
            except yaml.YAMLError:
                return None, body
    return {}, text


def format_paper_line(paper: dict):
    title = paper.get("title", "")
    author = paper.get("author", "")
    year = paper.get("year", "")
    journal = paper.get("journal", "")
    doi = paper.get("doi", "")
    arxiv = paper.get("arxiv_id", "")
    parts = [p for p in [author, f"*{title}*", journal, str(year) if year else ""] if p]
    line = ", ".join(parts)
    detail = []
    if doi:
        detail.append(f"DOI: {doi}")
    if arxiv:
        detail.append(f"arXiv: {arxiv}")
    if detail:
        line += " (" + "; ".join(detail) + ")"
    return f"- {line}"


def has_papers_section(body: str):
    return "## 经典论文与原始文献" in body or "### 经典论文与原始文献" in body


def process_file(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None:
        return False

    title = fm.get("title", "")
    stem = path.stem
    if is_report_like(title, stem):
        return False

    matched_papers = []
    for term, papers in LANDMARK_PAPERS.items():
        if term in title or term in stem:
            matched_papers.extend(papers)

    if not matched_papers:
        return False

    refs = fm.get("references") or {}
    existing_papers = refs.get("papers") or []
    existing_titles = {p.get("title") for p in existing_papers}
    added_frontmatter = 0
    for paper in matched_papers:
        if paper["title"] not in existing_titles:
            existing_papers.append(paper)
            existing_titles.add(paper["title"])
            added_frontmatter += 1

    changed = False
    if added_frontmatter:
        refs["papers"] = existing_papers
        fm["references"] = refs
        changed = True

    # 无论是否银层，都确保正文可见 DOI/arXiv
    if not has_papers_section(body):
        section_lines = ["", "---", "", "## 经典论文与原始文献", ""]
        for paper in matched_papers:
            section_lines.append(format_paper_line(paper))
        section_lines.append("")
        body = body.rstrip() + "\n" + "\n".join(section_lines)
        changed = True

    if not changed:
        return False

    new_text = (
        "---\n"
        + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
        + "---\n"
        + body
    )
    path.write_text(new_text, encoding="utf-8")
    return True


def main():
    changed = 0
    for p in PROJECT_ROOT.rglob("*.md"):
        if any(x in p.parts for x in ("node_modules", ".git", "00-归档", "归档")):
            continue
        if process_file(p):
            changed += 1
    print(f"Injected landmark papers into {changed} docs.")


if __name__ == "__main__":
    main()
